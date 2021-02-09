use std::io::{Read, Result, Write};

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct ChunkId(pub [u8; 4]);

const RIFF_ID: ChunkId = ChunkId(*b"RIFF");
const LIST_ID: ChunkId = ChunkId(*b"LIST");
const SEQT_ID: ChunkId = ChunkId(*b"seqt");

impl ChunkId {
    fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Whether the id is a known list chunk id.
    ///
    /// The function returns true only if the id is one of `b"RIFF"`, `b"LIST"` or `b"seqt"`
    fn has_subchunks(&self) -> bool {
        *self == RIFF_ID || *self == LIST_ID || *self == SEQT_ID
    }

    /// Whether the id is a known list chunk id, and has a form type designator.
    ///
    /// "seqt" chunks don't have form type designators.
    fn has_form_type(&self) -> bool {
        *self == RIFF_ID || *self == LIST_ID
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct Chunk {
    pub id: ChunkId,
    pub content: ChunkContent,
}

impl Chunk {
    fn new(id: ChunkId, content: ChunkContent) -> Chunk {
        Chunk { id, content }
    }

    pub fn new_riff(form_id: ChunkId, subchunks: Vec<Chunk>) -> Chunk {
        Chunk::new(
            RIFF_ID,
            ChunkContent::List {
                form_type: Some(form_id),
                subchunks,
            },
        )
    }

    pub fn new_data(form_id: ChunkId, content: Vec<u8>) -> Chunk {
        Chunk::new(form_id, ChunkContent::Subchunk(content))
    }
}

/// The contents of a chunk
#[derive(PartialEq, Eq, Debug)]
pub enum ChunkContent {
    /// The contents of a `RIFF`, `LIST`, or `seqt` chunk
    List {
        /// The type of list form
        form_type: Option<ChunkId>,

        /// The contained subchunks
        subchunks: Vec<Chunk>,
    },

    /// The contents of a terminal chunk
    Subchunk(Vec<u8>),
}

fn read_id(reader: &mut impl Read) -> Result<ChunkId> {
    let mut fourcc = [0; 4];
    reader.read_exact(&mut fourcc)?;
    Ok(ChunkId(fourcc))
}

fn read_header(reader: &mut impl Read) -> Result<(ChunkId, u32)> {
    let id = read_id(reader)?;
    let mut length = [0; 4];
    reader.read_exact(&mut length)?;
    let length = u32::from_le_bytes(length);
    Ok((id, length))
}

/// Reads a chunk. Returns the read chunk and the number of bytes read.
pub fn read_chunk(reader: &mut impl Read) -> Result<(Chunk, u32)> {
    let (id, len) = read_header(reader)?;
    if id.has_subchunks() {
        let form_type = if id.has_form_type() {
            Some(read_id(reader)?)
        } else {
            None
        };
        let mut count: u32 = if id.has_form_type() { 4 } else { 0 };
        let mut subchunks: Vec<Chunk> = Vec::new();
        while count < len {
            let (chunk, chunk_len) = read_chunk(reader)?;
            subchunks.push(chunk);
            count = count + chunk_len + 8;
        }
        Ok((
            Chunk::new(
                id,
                ChunkContent::List {
                    form_type,
                    subchunks,
                },
            ),
            count,
        ))
    } else {
        let padded_len = len + len % 2;
        let mut data: Vec<u8> = vec![0; padded_len as usize];
        reader.read_exact(&mut data)?;
        data.resize(len as usize, 0);
        Ok((Chunk::new_data(id, data), padded_len))
    }
}

fn calc_len(chunks: &[Chunk]) -> u32 {
    chunks
        .iter()
        .map(|chunk| match &chunk.content {
            ChunkContent::Subchunk(data) => {
                let len = data.len() as u32;
                len + len % 2 + 8
            }
            ChunkContent::List {
                form_type,
                subchunks,
            } => {
                let metadata_len = if form_type.is_some() { 12 } else { 8 };
                metadata_len + calc_len(&subchunks)
            }
        })
        .sum()
}

/// Writes a chunk to a stream.
pub fn write_chunk(writer: &mut impl Write, chunk: &Chunk) -> Result<()> {
    writer.write_all(&chunk.id.0)?;
    match &chunk.content {
        ChunkContent::Subchunk(v) => {
            let len = v.len() as u32;
            writer.write_all(&u32::to_le_bytes(len))?;
            writer.write_all(&v)?;
            if len % 2 != 0 {
                writer.write_all(&[0])?;
            }
        }
        ChunkContent::List {
            form_type,
            subchunks,
        } => {
            let len = calc_len(&subchunks);
            writer.write_all(&u32::to_le_bytes(if form_type.is_some() {
                len + 4
            } else {
                len
            }))?;
            if let Some(form_type) = form_type {
                writer.write_all(form_type.as_bytes())?;
            }
            for subchunk in subchunks {
                write_chunk(writer, subchunk)?;
            }
        }
    }
    Ok(())
}
