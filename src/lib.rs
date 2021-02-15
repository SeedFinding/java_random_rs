pub const JAVA_LCG: LCG = LCG { multiplier: 0x5DEECE66D, addend: 0xB };

#[derive(Copy, Clone, Debug)]
pub struct LCG {
    pub multiplier: u64,
    pub addend: u64,
}

impl LCG {
    pub fn modulo(&self, n: u64) -> u64 {
        n & mask(48)
    }

    pub fn combine(&self, steps: u64) -> LCG {
        let mut multiplier: u64 = 1u64;
        let mut addend: u64 = 0u64;
        let mut intermediate_multiplier = self.multiplier;
        let mut intermediate_addend = self.addend;
        let mut k: u64 = steps;
        while k != 0 {
            if (k & 1) != 0 {
                multiplier = multiplier.wrapping_mul(intermediate_multiplier);
                addend = intermediate_multiplier.wrapping_mul(addend).wrapping_add(intermediate_addend);
            }

            intermediate_addend = (intermediate_multiplier.wrapping_add(1)).wrapping_mul(intermediate_addend);
            intermediate_multiplier = intermediate_multiplier.wrapping_mul(intermediate_multiplier);
            k >>= 1;
        }

        return LCG { multiplier: self.modulo(multiplier ), addend: self.modulo(addend) };
    }

    pub fn combine_with_lcg(&self, lcg: LCG) -> LCG {
        return LCG {
            multiplier: self.multiplier * lcg.multiplier,
            addend: self.addend * lcg.multiplier + lcg.addend,
        };
    }
}

// Constants used to reverse operations
pub mod lcg_const_extra {
    pub const INV_A: u64 = 0xdfe05bcb1365;
    pub const INV_A_1: u64 = 18698324575379;
    pub const INV__INV_A__1: u64 = 192407907957609;
}


pub const fn mask(n: u8) -> u64 {
    (1 << n) - 1
}


#[cfg(test)]
mod lcg_test {
    use crate::{Random, JAVA_LCG, LCG};

    #[test]
    fn test_init() {
        let random: Random = Random::with_seed(12);
        assert_eq!(random.get_raw_seed(), 12 ^ JAVA_LCG.multiplier);
        assert_eq!(random.get_seed(), 12);
    }

    #[test]
    fn test_raw_init() {
        let random: Random = Random::with_raw_seed(12);
        assert_eq!(random.get_seed(), 12 ^ JAVA_LCG.multiplier);
        assert_eq!(random.get_raw_seed(), 12);
    }

    #[test]
    fn test_skip() {
        let mut random: Random = Random::with_raw_seed(12);
        let mut random2: Random = Random::with_raw_seed(12);
        let skip_random: Random = Random::with_seed_and_lcg(0, LCG { multiplier: 25214903917, addend: 11 });
        random.skip(skip_random);
        random2.next_state();
        assert_eq!(random.get_seed(), random2.get_seed())
    }

    #[test]
    fn test_skip_large() {
        let mut random: Random = Random::with_raw_seed(12);
        let mut random2: Random = Random::with_raw_seed(12);
        let skip_random: Random = Random::with_seed_and_lcg(0, LCG { multiplier: 56259567741473, addend: 137246343697672 });
        random.skip(skip_random);
        random2.next_state_n(1101000);
        assert_eq!(random.get_seed(), random2.get_seed())
    }

    #[test]
    fn test_advance() {
        let mut random: Random = Random::with_raw_seed(12);
        let mut random2: Random = Random::with_raw_seed(12);
        random.advance(LCG { multiplier: 56259567741473, addend: 137246343697672 });
        random2.next_state_n(1101000);
        assert_eq!(random.get_seed(), random2.get_seed())
    }


    #[test]
    fn test_advance_combine() {
        let mut random: Random = Random::with_raw_seed(12);
        let mut random2: Random = Random::with_raw_seed(12);
        dbg!(JAVA_LCG.combine(1101000));
        random.advance(JAVA_LCG.combine(1101000));
        random2.next_state_n(1101000);
        assert_eq!(random.get_seed(), random2.get_seed())
    }
}


#[derive(Copy, Clone, Debug)]
pub struct Random {
    seed: u64,
    lcg: LCG,
}

impl Random {
    pub fn with_seed(s: u64) -> Random {
        let mut r = Random { seed: 0, lcg: JAVA_LCG };
        r.set_seed(s);
        r
    }
    pub fn with_seed_and_lcg(s: u64, lcg: LCG) -> Random {
        let mut r = Random { seed: 0, lcg };
        r.set_seed(s);
        r
    }

    pub fn with_raw_seed(s: u64) -> Random {
        let mut r = Random { seed: 0, lcg: JAVA_LCG };
        r.set_raw_seed(s);
        r
    }
    pub fn with_raw_seed_and_lcg(s: u64, lcg: LCG) -> Random {
        let mut r = Random { seed: 0, lcg };
        r.set_raw_seed(s);
        r
    }
    pub fn default_scramble(s: u64) -> u64 {
        s ^ JAVA_LCG.multiplier
    }
    pub fn set_seed(&mut self, s: u64) {
        self.seed = s ^ self.lcg.multiplier;
    }

    pub fn set_raw_seed(&mut self, s: u64) {
        self.seed = s;
    }

    pub fn get_seed(&self) -> u64 {
        (self.seed ^ self.lcg.multiplier) & mask(48)
    }

    pub fn get_raw_seed(&self) -> u64 {
        self.seed & mask(48)
    }

    pub fn advance(&mut self, lcg: LCG) -> Random {
        self.seed = self.seed.wrapping_mul(lcg.multiplier).wrapping_add(lcg.addend);
        *self
    }

    pub fn next_state(&mut self) -> Random {
        self.advance(self.lcg)
    }

    pub fn next_state_n(&mut self, n: u32) -> Random {
        // please prefer generating another lcg
        for _ in 0..n {
            self.next_state();
        }
        *self
    }

    pub fn skip(&mut self, skip_random: Random) -> Random {
        self.advance(skip_random.lcg)
    }

    pub fn next(&mut self, bits: u8) -> i32 {
        self.next_state();
        ((self.seed & mask(48)) >> (48 - bits)) as i32
    }

    // Returns the same as the last call to next
    pub fn last_next(&self, bits: u8) -> i32 {
        ((self.seed & mask(48)) >> (48 - bits)) as i32
    }

    pub fn next_int(&mut self) -> i32 {
        self.next(32)
    }

    pub fn next_int_n(&mut self, n: i32) -> i32 {
        if !(n > 0) {
            panic!("In JavaRng::next_int_n, n should be greater than zero.");
        }
        // If n is a power of 2
        if (n & -n) == n {
            return (((n as i64) * (self.next(31) as i64)) >> 31) as i32;
        }

        let mut bits;
        let mut val;
        loop {
            bits = self.next(31);
            val = bits % n;
            // Check for modulo bias
            if bits.wrapping_sub(val).wrapping_add(n - 1) >= 0 {
                break;
            }
        }

        val
    }

    pub fn next_long(&mut self) -> i64 {
        ((self.next_int() as i64) << 32) + (self.next_int() as i64)
    }

    pub fn next_boolean(&mut self) -> bool {
        self.next(1) != 0
    }

    pub fn next_float(&mut self) -> f32 {
        self.next(24) as f32 / (1 << 24) as f32
    }

    pub fn next_double(&mut self) -> f64 {
        let hi = (self.next(26) as i64) << 27;
        let lo = self.next(27) as i64;

        (hi + lo) as f64 / ((1u64 << 53) as f64)
    }

    // The inverse of next()
    pub fn previous(&mut self) {
        self.seed = Self::previous_state(self.seed);
    }

    // The previous internal state of the prng, not the seed
    pub fn previous_state(s: u64) -> u64 {
        (s.wrapping_sub(JAVA_LCG.addend)).wrapping_mul(lcg_const_extra::INV_A) & mask(48)
    }
}

