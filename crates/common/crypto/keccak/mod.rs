#[cfg(all(target_arch = "aarch64", target_os = "linux"))]
core::arch::global_asm!(include_str!("keccak1600-armv8-elf.s"), options(raw));
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
core::arch::global_asm!(include_str!("keccak1600-armv8-macho.s"), options(raw));
#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(include_str!("keccak1600-x86_64.s"), options(att_syntax));

pub use imp::*;

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
mod imp {
    const BLOCK_SIZE: usize = 136;

    #[derive(Default, Clone, Copy)]
    #[repr(transparent)]
    struct State([u64; 25]);

    unsafe extern "C" {
        #[link_name = "ethrex_SHA3_absorb"]
        unsafe fn ethrex_SHA3_absorb(state: *mut State, buf: *const u8, len: usize, r: usize) -> usize;
        unsafe fn ethrex_SHA3_squeeze(state: *mut State, buf: *mut u8, len: usize, r: usize);
    }

    pub fn keccak_hash(data: impl AsRef<[u8]>) -> [u8; 32] {
        let data = data.as_ref();
        if data.len() <= memo::MAX_LEN {
            return memo::hash(data);
        }
        let mut state = Keccak256::new();
        state.update(data);
        state.finalize()
    }

    /// Small inputs (addresses, slot keys, log topics, mapping keys) recur across a block's
    /// replays far more often than they change, so their hashes are kept in a direct-mapped
    /// table. Each entry is a seqlock over atomics: a reader only trusts a full, unchanged copy
    /// of the input and length, so a hit is exactly the keccak of the same bytes.
    mod memo {
        use core::sync::atomic::{AtomicU64, Ordering, fence};

        pub const MAX_LEN: usize = 64;
        const ENTRIES: usize = 1 << 15;
        const WORDS: usize = 14;

        #[allow(clippy::declare_interior_mutable_const)]
        const ZERO: AtomicU64 = AtomicU64::new(0);
        #[allow(clippy::declare_interior_mutable_const)]
        const ENTRY: [AtomicU64; WORDS] = [ZERO; WORDS];
        static TABLE: [[AtomicU64; WORDS]; ENTRIES] = [ENTRY; ENTRIES];

        pub fn hash(data: &[u8]) -> [u8; 32] {
            let mut input = [0u64; 8];
            for (word, chunk) in input.iter_mut().zip(data.chunks(8)) {
                let mut bytes = [0u8; 8];
                bytes[..chunk.len()].copy_from_slice(chunk);
                *word = u64::from_le_bytes(bytes);
            }
            let len = data.len() as u64;
            let mut index = len.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            for word in input {
                index = (index.rotate_left(5) ^ word).wrapping_mul(0x51_7cc1_b727_220a_95);
            }
            #[allow(clippy::indexing_slicing)]
            let entry = &TABLE[(index >> 49) as usize & (ENTRIES - 1)];

            let seq = entry[0].load(Ordering::Acquire);
            if seq & 1 == 0 && entry[1].load(Ordering::Relaxed) == len + 1 {
                let same = input
                    .iter()
                    .zip(&entry[2..10])
                    .all(|(word, slot)| *word == slot.load(Ordering::Relaxed));
                let mut out = [0u8; 32];
                for (chunk, slot) in out.chunks_mut(8).zip(&entry[10..14]) {
                    chunk.copy_from_slice(&slot.load(Ordering::Relaxed).to_le_bytes());
                }
                fence(Ordering::Acquire);
                if same && entry[0].load(Ordering::Relaxed) == seq {
                    return out;
                }
            }

            let mut state = super::Keccak256::new();
            state.update(data);
            let out = state.finalize();

            if seq & 1 == 0
                && entry[0]
                    .compare_exchange(seq, seq + 1, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
            {
                fence(Ordering::Release);
                entry[1].store(len + 1, Ordering::Relaxed);
                for (word, slot) in input.iter().zip(&entry[2..10]) {
                    slot.store(*word, Ordering::Relaxed);
                }
                for (chunk, slot) in out.chunks(8).zip(&entry[10..14]) {
                    let mut bytes = [0u8; 8];
                    bytes.copy_from_slice(chunk);
                    slot.store(u64::from_le_bytes(bytes), Ordering::Relaxed);
                }
                entry[0].store(seq + 2, Ordering::Release);
            }
            out
        }
    }

    #[derive(Clone)]
    pub struct Keccak256 {
        state: State,
        tail_buf: [u8; BLOCK_SIZE],
        tail_len: usize,
    }

    impl Default for Keccak256 {
        fn default() -> Self {
            Self {
                state: State::default(),
                tail_buf: [0; BLOCK_SIZE],
                tail_len: 0,
            }
        }
    }

    impl Keccak256 {
        #[inline]
        pub fn new() -> Self {
            Self::default()
        }

        #[inline]
        pub fn update(&mut self, data: impl AsRef<[u8]>) -> Self {
            let mut data = data.as_ref();
            unsafe {
                // partial block
                if self.tail_len > 0 {
                    let need = BLOCK_SIZE - self.tail_len;
                    if data.len() < need {
                        // still partial block
                        self.tail_buf[self.tail_len..self.tail_len + data.len()]
                            .copy_from_slice(data);
                        self.tail_len += data.len();
                        return self.clone();
                    }

                    // complete block
                    self.tail_buf[self.tail_len..BLOCK_SIZE].copy_from_slice(&data[..need]);

                    ethrex_SHA3_absorb(
                        &mut self.state,
                        self.tail_buf.as_ptr(),
                        self.tail_buf.len(),
                        BLOCK_SIZE,
                    );

                    self.tail_len = 0;
                    self.tail_buf.fill(0);
                    data = &data[need..];
                }
            }

            match data {
                [] => {}
                data if data.len() < BLOCK_SIZE => unsafe {
                    self.tail_len = data.len();
                    self.tail_buf
                        .get_unchecked_mut(..self.tail_len)
                        .copy_from_slice(data);
                },
                data => unsafe {
                    let rem = ethrex_SHA3_absorb(&mut self.state, data.as_ptr(), data.len(), BLOCK_SIZE);
                    self.tail_len = rem;
                    if rem != 0 {
                        let tail_data = data.get_unchecked(data.len() - rem..);
                        self.tail_buf
                            .get_unchecked_mut(..rem)
                            .copy_from_slice(tail_data);
                    }
                },
            }
            self.clone()
        }

        #[inline]
        pub fn finalize(mut self) -> [u8; 32] {
            let mut hash_buf = [0u8; 32];

            unsafe {
                *self.tail_buf.get_unchecked_mut(self.tail_len) = 0x01;
                *self.tail_buf.get_unchecked_mut(BLOCK_SIZE - 1) |= 0x80;

                ethrex_SHA3_absorb(
                    &mut self.state,
                    self.tail_buf.as_ptr(),
                    self.tail_buf.len(),
                    BLOCK_SIZE,
                );

                ethrex_SHA3_squeeze(
                    &mut self.state,
                    hash_buf.as_mut_ptr(),
                    hash_buf.len(),
                    BLOCK_SIZE,
                );
            }

            hash_buf
        }
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
mod imp {
    use tiny_keccak::{Hasher, Keccak};

    pub fn keccak_hash(data: impl AsRef<[u8]>) -> [u8; 32] {
        let mut out = [0u8; 32];
        let mut h = Keccak::v256();
        h.update(data.as_ref());
        h.finalize(&mut out);
        out
    }

    #[derive(Clone)]
    pub struct Keccak256 {
        h: Keccak,
    }

    impl Default for Keccak256 {
        fn default() -> Self {
            Self::new()
        }
    }

    impl Keccak256 {
        #[inline]
        pub fn new() -> Self {
            Self { h: Keccak::v256() }
        }

        #[inline]
        pub fn update(&mut self, data: impl AsRef<[u8]>) -> Self {
            let d = data.as_ref();
            if !d.is_empty() {
                self.h.update(d);
            }
            self.clone()
        }

        #[inline]
        pub fn finalize(self) -> [u8; 32] {
            let mut out = [0u8; 32];
            self.h.finalize(&mut out);
            out
        }
    }
}
