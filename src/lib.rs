//! # WAV
//!
//! Reading and Writing simple subset of the WAVE audio files.
//!
//! # Examples
//!
//! Generate one second sample of base A note at maximum volume and store it in file "sine.wav".
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use std::f64::consts::PI;
//! use std::fs::File;
//!
//! use wav::{BitDepth, Channels, Format, PCMData};
//!
//! let amplitude = i16::MAX as f64; // maximum
//! let frequency = 440.0; // base A note
//!
//! let samples = (0..44_100)
//!     .map(|i| i as f64 / 44_100.0) // convert sample index to time
//!     .map(|t| amplitude * (t * frequency * 2.0 * PI).sin()) // sine wave
//!     .map(|s| s as i16)
//!     .collect::<Vec<_>>();
//!
//! let mut file = File::create("target/sine.wav")?;
//! let fmt = Format::new(
//!     Channels::Mono,
//!     44_100,
//!     BitDepth::B16,
//! );
//!
//! wav::write(fmt, PCMData::B16(samples), &mut file)?;
//! # Ok(())
//! # }
//! ```
//!
//! Generate one second sample of base A note in left channel and and one octave higher in right
//! channel.
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use std::f64::consts::PI;
//! use std::fs::File;
//!
//! use wav::{BitDepth, Channels, Format, PCMData};
//!
//! let amplitude = i16::MAX as f64; // maximum
//! let frequency = 440.0; // base A note
//!
//! let samples = (0..44_100)
//!     .map(|i| i as f64 / 44_100.0) // convert sample index to time
//!     .flat_map(|t| vec![
//!         amplitude * (t * frequency * 2.0 * PI).sin(),         // base note
//!         amplitude * (t * (2.0 * frequency) * 2.0 * PI).sin(), // one octave higher
//!     ])
//!     .map(|s| s as i16)
//!     .collect::<Vec<_>>();
//!
//! let mut file = File::create("target/sine2.wav")?;
//! let fmt = Format::new(
//!     Channels::Stereo,
//!     44_100,
//!     BitDepth::B16,
//! );
//!
//! wav::write(fmt, PCMData::B16(samples), &mut file)?;
//! # Ok(())
//! # }
//! ```
//!
//! Read a mono WAVE file (from the first example) and calculate its RMS value.
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use std::convert::TryInto;
//! use std::f64::consts::PI;
//! use std::fs::File;
//!
//! use wav::{BitDepth, Channels, Format, PCMData};
//!
//! let mut file = File::open("target/sine.wav")?;
//! let (format, pcm_data) = wav::read(&mut file)?;
//!
//! let fmt = Format::new(
//!     Channels::Mono,
//!     44_100,
//!     BitDepth::B16,
//! );
//! assert_eq!(format, fmt);
//!
//! let pcm_data = match pcm_data {
//!     PCMData::B16(data) => data,
//!     _ => unreachable!(),
//! };
//!
//! let len = pcm_data.len() as f64;
//! let sum = pcm_data.into_iter()
//!     .map(|sample| ((sample as f64) / (i16::MAX as f64)).powi(2))
//!     .sum::<f64>();
//! let rms = (sum / len).sqrt();
//!
//! // formula for RMS of sine wave with amplitude 1
//! let sine_wave_rms = 1.0 / (2.0_f64).sqrt();
//!
//! assert!( (rms - sine_wave_rms).abs() < 0.001 );
//!
//! # Ok(())
//! # }
//! ```

mod riff;

use riff::{Chunk, ChunkContent, ChunkId};
use std::io::{Read, Result, Write};

const WAVE_ID: ChunkId = ChunkId(*b"WAVE");
const FMT_ID: ChunkId  = ChunkId(*b"fmt ");
const DATA_ID: ChunkId = ChunkId(*b"data");

/// Specifies PCM audio format in the "fmt " chunk audio_format field
pub const AUDIO_FORMAT_PCM: u16 = 1;

macro_rules! error {
    ( $fmt:literal $(, $val:expr)* $(,)? ) => {
        ::std::io::Error::new(
            ::std::io::ErrorKind::Other,
            ::std::format!($fmt $(, $val)*),
        )
    };
}

/// WAVE file "fmt " chunk
///
/// This struct only supports PCM data, there are no extra members for compressed format data.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct Format {
    pub audio_format: u16,
    pub channel_count: u16,
    pub sampling_rate: u32,
    pub bytes_per_second: u32,
    pub bytes_per_sample: u16,
    pub bits_per_sample: u16,
}

/// Audio channels (mono or stereo)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum Channels {
    /// Single channel
    Mono   = 1,
    /// Two channels, usually interpreted as Left and Right
    Stereo = 2,
}

/// Bit-depths for PCM data (8, 16 or 24)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum BitDepth {
    B8  = 8,
    B16 = 16,
    B24 = 24,
}

/// PCM (Pulse-code modulation) samples data
///
/// Can be crated from raw bytes or from `Vec<u8>`, `Vec<i16>` or `Vec<i32>` samples.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PCMData {
    B8(Vec<u8>),
    B16(Vec<i16>),
    B24(Vec<i32>),
}

impl Format {
    /// Creates new Format struct from restricted values.
    ///
    /// For unrestricted values use [`Format::new_raw`].
    ///
    /// # Example
    ///
    /// ```
    /// let fmt = wav::Format::new(
    ///     wav::Channels::Mono,
    ///     44_100,
    ///     wav::BitDepth::B16,
    /// );
    ///
    /// assert_eq!(fmt.audio_format, 1);
    /// assert_eq!(fmt.channel_count, 1);
    /// assert_eq!(fmt.sampling_rate, 44_100);
    /// assert_eq!(fmt.bytes_per_second, 16 * 44_100 / 8);
    /// assert_eq!(fmt.bytes_per_sample, 16 / 8);
    /// assert_eq!(fmt.bits_per_sample, 16);
    /// ```
    pub fn new(channels: Channels, sampling_rate: u32, bit_depth: BitDepth) -> Self {
        assert!(sampling_rate > 0, "Sampling rate must be grater than 0");
        Format::new_raw(
            AUDIO_FORMAT_PCM,
            channels as u16,
            sampling_rate,
            bit_depth as u16,
        )
    }

    /// Creates new Format struct from raw values.
    ///
    /// # Parameters
    ///
    /// * `audio_format` - Audio format. `wav::AUDIO_FORMAT_PCM` for uncompressed PCM data.
    /// * `channel_count` - Channel count, the number of channels each sample has.
    ///                     Usually 1 (mono) or 2 (stereo).
    /// * `sampling_rate` - Sampling rate in Hertz (e.g. 44.1kHz, 48kHz, 96kHz, etc.
    ///                     would translate to 44_100, 48_000, 96_000)
    /// * `bits_per_sample` - Number of bits in each (sub-channel) sample.
    ///                       Usually 8, 16, or 24.
    ///
    /// # Example
    ///
    /// ```
    /// let fmt = wav::Format::new_raw(wav::AUDIO_FORMAT_PCM, 2, 44_100, 16);
    ///
    /// assert_eq!(fmt.audio_format, 1);
    /// assert_eq!(fmt.channel_count, 2);
    /// assert_eq!(fmt.sampling_rate, 44_100);
    /// assert_eq!(fmt.bytes_per_second, 16 * 2 * 44_100 / 8);
    /// assert_eq!(fmt.bytes_per_sample, 16 * 2 / 8);
    /// assert_eq!(fmt.bits_per_sample, 16);
    /// ```
    pub fn new_raw(
        audio_format: u16,
        channel_count: u16,
        sampling_rate: u32,
        bits_per_sample: u16,
    ) -> Self {
        Format {
            audio_format,
            channel_count,
            sampling_rate,
            bytes_per_second: (((bits_per_sample >> 3) * channel_count) as u32) * sampling_rate,
            bytes_per_sample: ((bits_per_sample >> 3) * channel_count) as u16,
            bits_per_sample,
        }
    }

    fn from_raw_bytes(v: &[u8]) -> Option<Self> {
        if v.len() < 16 {
            return None;
        }
        Some(Format {
            audio_format: u16::from_le_bytes([v[0], v[1]]),
            channel_count: u16::from_le_bytes([v[2], v[3]]),
            sampling_rate: u32::from_le_bytes([v[4], v[5], v[6], v[7]]),
            bytes_per_second: u32::from_le_bytes([v[8], v[9], v[10], v[11]]),
            bytes_per_sample: u16::from_le_bytes([v[12], v[13]]),
            bits_per_sample: u16::from_le_bytes([v[14], v[15]]),
        })
    }

    fn into_raw_bytes(self) -> [u8; 16] {
        let mut v: [u8; 16] = [0; 16];
        v[0..2].copy_from_slice(&self.audio_format.to_le_bytes());
        v[2..4].copy_from_slice(&self.channel_count.to_le_bytes());
        v[4..8].copy_from_slice(&self.sampling_rate.to_le_bytes());
        v[8..12].copy_from_slice(&self.bytes_per_second.to_le_bytes());
        v[12..14].copy_from_slice(&self.bytes_per_sample.to_le_bytes());
        v[14..16].copy_from_slice(&self.bits_per_sample.to_le_bytes());
        v
    }
}

impl PCMData {
    /// Coverts raw bytes into PCMData of `bit_depth`.
    ///
    /// Ignores trailing garbage bytes when the lenght isn't a multiple of `bit_depth`.
    pub fn from_raw_bytes(bytes: Vec<u8>, bit_depth: BitDepth) -> PCMData {
        match bit_depth {
            BitDepth::B8 => PCMData::B8(bytes),
            BitDepth::B16 => PCMData::B16(
                bytes
                    .chunks_exact(2)
                    .map(|s| i16::from_le_bytes([s[0], s[1]]))
                    .collect::<Vec<_>>(),
            ),
            BitDepth::B24 => PCMData::B24(
                bytes
                    .chunks_exact(3)
                    .map(|s| i32::from_le_bytes([s[0], s[1], s[2], 0]))
                    .collect::<Vec<_>>(),
            ),
        }
    }

    /// Converts PCMData into raw bytes.
    pub fn into_raw_bytes(self) -> Vec<u8> {
        match self {
            PCMData::B8(data) => data,
            PCMData::B16(v) => {
                let mut output = Vec::new();
                v.into_iter().for_each(|s| output.extend(&s.to_le_bytes()));
                output
            }
            PCMData::B24(v) => {
                let mut output = Vec::new();
                v.into_iter()
                    .for_each(|s| output.extend(&s.to_le_bytes()[0..3]));
                output
            }
        }
    }

    /// Returns bit depth of PCMData.
    pub fn bit_depth(&self) -> BitDepth {
        match self {
            PCMData::B8(_) => BitDepth::B8,
            PCMData::B16(_) => BitDepth::B16,
            PCMData::B24(_) => BitDepth::B24,
        }
    }
}

/// Reads the input and attempts to extract the audio data and header from it.
///
/// # Errors
///
/// This function fails if:
/// * The input couldn't be opened or read.
/// * The input isn't a RIFF file.
/// * The WAVE data is malformed.
/// * The WAVE header specifies any other format than uncompressed PCM.
pub fn read(reader: &mut impl Read) -> Result<(Format, PCMData)> {
    let (wav, _) = riff::read_chunk(reader)?;

    let wav_chunks = match wav.content {
        ChunkContent::List {
            form_type: Some(WAVE_ID),
            subchunks,
        } => subchunks,
        _ => {
            return Err(error!("RIFF file type is not \"WAVE\""));
        }
    };

    // find format chunk
    let fmt = wav_chunks
        .iter()
        .find_map(|chunk| match &chunk.content {
            ChunkContent::Subchunk(v) if chunk.id == FMT_ID => Some(v.as_slice()),
            _ => None,
        })
        .ok_or_else(|| error!("WAVE file is missing \"fmt \" chunk"))?;

    // parse format chunk
    let fmt = Format::from_raw_bytes(fmt)
        .ok_or_else(|| error!(
            "Malformed \"fmt \" chunk (expected {} bytes chunk is {} bytes)",
            std::mem::size_of::<Format>(),
            fmt.len(),
        ))?;

    // check file is using PCM data format
    if fmt.audio_format != AUDIO_FORMAT_PCM {
        return Err(error!(
            "Only uncompressed PCM format (1) is supported, file specifies {}",
            fmt.audio_format,
        ));
    }

    // parses file bit depth
    let bit_depth = match fmt.bits_per_sample {
        8 => BitDepth::B8,
        16 => BitDepth::B16,
        24 => BitDepth::B24,
        _ => {
            return Err(error!(
                "Only bit-dephts of 8, 16 and 24 are supported, file specifies {}",
                fmt.bits_per_sample,
            ));
        }
    };

    let data = wav_chunks
        .into_iter()
        .filter_map(|chunk| match chunk.content {
            ChunkContent::Subchunk(v) if chunk.id == DATA_ID => Some(v),
            _ => None,
        })
        .map(|bytes| PCMData::from_raw_bytes(bytes, bit_depth))
        .next()
        .ok_or_else(|| error!("WAVE file is missing \"data\" chunk"))?;

    Ok((fmt, data))
}

/// Writes the WAVE data into the given output.
///
/// The function doesn't check whether the format makes sense apart from bit-depth.
/// Use [`Format::new`] for creating sane values.
///
/// # Errors
///
/// This function fails if:
/// * The output cannot be opened or written to.
/// * Bit-depths of `track` and `fmt` don't match.
pub fn write(fmt: Format, data: PCMData, writer: &mut impl Write) -> Result<()> {
    if data.bit_depth() as u16 != fmt.bits_per_sample {
        return Err(error!(
            "Bit-depths don't match fmt={}, data={}",
            data.bit_depth() as u16,
            fmt.bits_per_sample,
        ));
    }

    let fmt_chunk = Chunk::new_data(FMT_ID, Vec::from(fmt.into_raw_bytes()));
    let data_chunk = Chunk::new_data(DATA_ID, data.into_raw_bytes());

    riff::write_chunk(
        writer,
        &Chunk::new_riff(WAVE_ID, vec![fmt_chunk, data_chunk]),
    )
}
