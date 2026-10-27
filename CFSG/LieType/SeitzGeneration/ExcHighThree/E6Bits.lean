module

public import CFSG.LieType.Chevalley.RootConj

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree.E6Bits

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

@[expose] def col (A q : ℕ) : ℕ :=
  A / 2 ^ (78 * q) % 2 ^ 78

@[expose] def slots : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ (78 * n) * 1 + slots n

@[expose] def mulAux (A B : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (col A n * (B / 2 ^ n &&& slots 78)) ^^^ mulAux A B n

@[expose] def mul (A B : ℕ) : ℕ :=
  mulAux A B 78

@[expose] def pack : List ℕ → ℕ
  | [] => 0
  | a :: L => 2 ^ 78 * pack L + a % 2 ^ 78

@[expose] def maskOf (v : List (ℕ × ℤ)) : ℕ :=
  v.foldr (fun x m => if x.2 % 2 = 0 then m else m ^^^ 2 ^ x.1) 0

@[expose] def eltBits (a : ℕ) : List ℕ :=
  (List.range 78).map fun c => maskOf ((c, 1) :: (colOf (entries Tag.E6 a 1) c ++
    colOf (entries Tag.E6 a 2) c ++ colOf (entries Tag.E6 a 3) c))

abbrev idx (i : Fin 6) : Fin Tag.E6.rank :=
  Fin.cast rfl i

@[expose] def nBits (i : Fin 6) : List ℕ :=
  (List.range 78).map fun p => maskOf (nPos Tag.E6 (idx i) p)

@[expose] def oneBits : ℕ :=
  pack ((List.range 78).map (2 ^ ·))

@[expose] def xCols : Fin 6 → List ℕ
  | 0 =>
    [1, 2, 68, 8, 16, 32, 64, 128, 8448, 512, 1024, 2048, 4161, 8192, 16384, 32768, 65536,
     16908288, 262144, 524288, 1048576, 2097152, 4194304, 8454144, 16777216, 33554432,
     17246978048, 134217728, 268435456, 34896609280, 1073741824, 2147483648, 4294967296,
     8858370048, 17179869184, 34359738368, 68719476736, 137438953472, 35459249995776,
     549755813888, 1099511627776, 72567767433216, 4398046511104, 8864812498944, 18691697672192,
     35184372088832, 70368744177664, 140737488355328, 281474976710656, 18577348462903296,
     37154696925806592, 2251799813685248, 4644337115725824, 11258999068426240, 18014398509481984,
     36028797018963968, 72057594037927936, 144115188075855872, 4899916394579099648,
     648518346341351424, 1297036692682702848, 2305843009213693952, 4611686018427387904,
     9223372036854775808, 313594649253062377472, 36893488147419103232, 83010348331692982272,
     147573952589676412928, 295147905179352825856, 590295810358705651712, 1180591620717411303424,
     2951479051793528258560, 4722366482869645213696, 9444732965739290427392,
     18889465931478580854784, 37778931862957161709568, 75557863725914323419136,
     151115727451828646838272]
  | 1 =>
    [1, 2, 4, 136, 16, 32, 64, 128, 256, 33280, 1024, 2048, 4096, 8192, 16514, 32768, 65536,
     67239936, 262144, 134742016, 1048576, 2097152, 4194304, 8388608, 17196646400, 33816576,
     67108864, 134217728, 268435456, 275414777856, 1073741824, 551903297536, 4294967296,
     8589934592, 17179869184, 35218731827200, 68987912192, 138512695296, 274877906944,
     549755813888, 1099511627776, 1128098930098176, 4398046511104, 8804682956800, 17592186044416,
     35184372088832, 36099165763141632, 141836999983104, 285873023221760, 562949953421312,
     1125899906842624, 2251799813685248, 4521191813414912, 9007199254740992, 18014398509481984,
     36028797018963968, 72057594037927936, 146366987889541120, 288230376151711744,
     576460752303423488, 1161928703861587968, 2305843009213693952, 4611686018427387904,
     9223372036854775808, 18446744073709551616, 36893488147419103232, 73786976294838206464,
     147573952589676412928, 295147905179352825856, 590295810358705651712, 1180591620717411303424,
     2361183241434822606848, 4722366482869645213696, 9444732965739290427392,
     94447329657392904273920, 37778931862957161709568, 75557863725914323419136,
     188894659314785808547840]
  | 2 =>
    [257, 2, 4, 264, 16, 32, 8256, 128, 256, 131584, 1024, 2048, 4096, 8192, 16384, 67141632,
     65796, 131072, 262144, 537395200, 1048576, 2097152, 4194304, 8392704, 16777216, 33554432,
     67108864, 275012124672, 268697600, 536870912, 1073741824, 2201170739200, 4294967296,
     8589934592, 17179869184, 34359738368, 68753031168, 137438953472, 274877906944,
     1126449662656512, 1100585369600, 2199023255552, 4398046511104, 8796093022208,
     17592186044416, 35184372088832, 70368744177664, 140874927308800, 281474976710656,
     562949953421312, 1125899906842624, 2256197860196352, 4503599627370496, 9007199254740992,
     2323857407723175936, 36028797018963968, 72057594037927936, 144396663052566528,
     288230376151711744, 576460752303423488, 1152921504606846976, 2305843009213693952,
     152185638608103800832, 9223372036854775808, 18446744073709551616, 37469948899722526720,
     73786976294838206464, 147573952589676412928, 5017514388048998039552, 590295810358705651712,
     1254378597012249509888, 2361183241434822606848, 4722366482869645213696,
     11805916207174113034240, 18889465931478580854784, 37778931862957161709568,
     75557863725914323419136, 151115727451828646838272]
  | 3 =>
    [1, 514, 516, 8, 528, 32, 64, 32896, 131328, 512, 525312, 2048, 4096, 16785408, 16384, 32768,
     65536, 131072, 262664, 524288, 1048576, 2149580800, 4194304, 8388608, 16777216, 33570816,
     67108864, 134217728, 268500992, 536870912, 1074790400, 2147483648, 4294967296, 8598323200,
     17179869184, 34359738368, 68719476736, 137438953472, 563224831328256, 549755813888,
     1099511627776, 2199023255552, 4402341478400, 8796093022208, 17592186044416,
     18049582881570816, 70368744177664, 140737488355328, 281474976710656, 562949953421312,
     289356276058554368, 2251799813685248, 4503599627370496, 9007199254740992, 18014398509481984,
     4647714815446351872, 72198331526283264, 144115188075855872, 288230376151711744,
     580964351930793984, 1152921504606846976, 2305843009213693952, 4611686018427387904,
     9367487224930631680, 18446744073709551616, 36893488147419103232, 74939897799445053440,
     147573952589676412928, 295147905179352825856, 590295810358705651712, 1180591620717411303424,
     2361183241434822606848, 23611832414348226068480, 9444732965739290427392,
     18889465931478580854784, 47223664828696452136960, 75557863725914323419136,
     151115727451828646838272]
  | 4 =>
    [1, 2, 4, 1032, 16, 1056, 64, 128, 256, 524800, 1024, 2099200, 4096, 8192, 16384, 134250496,
     65536, 537001984, 262144, 524288, 1049616, 2097152, 4194304, 8388608, 34376515584, 33554432,
     274945015808, 134217728, 268435456, 536870912, 1074003968, 2147483648, 4299161600,
     8589934592, 35201551958016, 34359738368, 68719476736, 137472507904, 274877906944,
     549755813888, 1099780063232, 2199023255552, 4398046511104, 8796093022208, 17600775979008,
     35184372088832, 70368744177664, 140806207832064, 281474976710656, 562949953421312,
     1125899906842624, 2251799813685248, 4512395720392704, 9007199254740992, 18014398509481984,
     36028797018963968, 72057594037927936, 144115188075855872, 18734974449861263360,
     576460752303423488, 1152921504606846976, 2305843009213693952, 299759591197780213760,
     9223372036854775808, 18446744073709551616, 36893488147419103232, 73786976294838206464,
     4869940435459321626624, 295147905179352825856, 599519182395560427520,
     1180591620717411303424, 2434970217729660813312, 4722366482869645213696,
     10625324586456701730816, 18889465931478580854784, 37778931862957161709568,
     75557863725914323419136, 151115727451828646838272]
  | 5 =>
    [1, 2, 4, 8, 2064, 32, 64, 128, 256, 512, 2098176, 2048, 4096, 8192, 16384, 32768, 65536,
     131072, 262144, 2148007936, 1048576, 2097152, 4196384, 8388608, 16777216, 33554432,
     67108864, 549890031616, 268435456, 2199560126464, 1073741824, 2147483648, 4296015872,
     8589934592, 17179869184, 70403103916032, 68719476736, 137438953472, 1126174784749568,
     549755813888, 1099511627776, 2199023255552, 4399120252928, 8796093022208, 17592186044416,
     36063981391052800, 70368744177664, 140737488355328, 281612415664128, 288793326105133056,
     1125899906842624, 2252899325313024, 4503599627370496, 9024791440785408, 4629700416936869888,
     36028797018963968, 72057594037927936, 144255925564211200, 288230376151711744,
     576460752303423488, 1157425104234217472, 149879795598890106880, 4611686018427387904,
     9295429630892703744, 18446744073709551616, 36893488147419103232, 74363437047141629952,
     147573952589676412928, 295147905179352825856, 590295810358705651712, 1217485108864830406656,
     2361183241434822606848, 4722366482869645213696, 9444732965739290427392,
     18889465931478580854784, 37778931862957161709568, 75557863725914323419136,
     151115727451828646838272]

@[expose] def nCols : Fin 6 → List ℕ
  | 0 =>
    [1, 2, 5, 8, 16, 32, 4096, 128, 8192, 512, 1024, 2048, 64, 256, 16384, 32768, 8388608,
     16777216, 262144, 524288, 1048576, 2097152, 4194304, 65536, 131072, 33554432, 17179869184,
     134217728, 8589934592, 34359738368, 1073741824, 2147483648, 4294967296, 268435456, 67108864,
     536870912, 8796093022208, 137438953472, 35184372088832, 549755813888, 17592186044416,
     70368744177664, 4398046511104, 68719476736, 1099511627776, 274877906944, 2199023255552,
     4503599627370496, 281474976710656, 18014398509481984, 36028797018963968, 9007199254740992,
     140737488355328, 2251799813685248, 562949953421312, 1125899906842624, 576460752303423488,
     1152921504606846976, 4611686018427387904, 72057594037927936, 144115188075855872,
     2305843009213693952, 288230376151711744, 73786976294838206464, 295147905179352825856,
     36893488147419103232, 9223372036854775808, 147573952589676412928, 18446744073709551616,
     2361183241434822606848, 1180591620717411303424, 590295810358705651712,
     4722366482869645213696, 9444732965739290427392, 18889465931478580854784,
     37778931862957161709568, 75557863725914323419136, 151115727451828646838272]
  | 1 =>
    [1, 2, 4, 10, 16, 32, 64, 16384, 256, 32768, 1024, 2048, 4096, 8192, 128, 512, 65536,
     67108864, 33554432, 134217728, 1048576, 2097152, 4194304, 8388608, 17179869184, 262144,
     131072, 524288, 68719476736, 274877906944, 137438953472, 549755813888, 4294967296,
     8796093022208, 16777216, 35184372088832, 268435456, 1073741824, 536870912, 2147483648,
     140737488355328, 1125899906842624, 281474976710656, 8589934592, 4503599627370496,
     34359738368, 36028797018963968, 1099511627776, 4398046511104, 562949953421312,
     2199023255552, 144115188075855872, 17592186044416, 1152921504606846976, 18014398509481984,
     70368744177664, 72057594037927936, 2251799813685248, 288230376151711744, 576460752303423488,
     9007199254740992, 2305843009213693952, 4611686018427387904, 9223372036854775808,
     18446744073709551616, 36893488147419103232, 73786976294838206464, 147573952589676412928,
     295147905179352825856, 590295810358705651712, 1180591620717411303424,
     2361183241434822606848, 4722366482869645213696, 9444732965739290427392,
     75557863725914323419136, 151115727451828646838272, 18889465931478580854784,
     37778931862957161709568]
  | 2 =>
    [5, 2, 4, 12, 16, 32, 8192, 128, 65536, 131072, 1024, 2048, 8388608, 64, 16384, 67108864,
     256, 512, 268435456, 536870912, 1048576, 2097152, 4194304, 4096, 16777216, 68719476736,
     32768, 274877906944, 262144, 524288, 1099511627776, 2199023255552, 4294967296, 8589934592,
     17179869184, 34359738368, 33554432, 140737488355328, 134217728, 1125899906842624,
     1073741824, 2147483648, 2251799813685248, 8796093022208, 17592186044416, 35184372088832,
     70368744177664, 137438953472, 144115188075855872, 562949953421312, 549755813888,
     4398046511104, 4503599627370496, 9007199254740992, 2305843009213693952, 36028797018963968,
     72057594037927936, 281474976710656, 288230376151711744, 36893488147419103232,
     1152921504606846976, 18014398509481984, 147573952589676412928, 9223372036854775808,
     18446744073709551616, 576460752303423488, 1180591620717411303424, 4611686018427387904,
     4722366482869645213696, 590295810358705651712, 73786976294838206464, 9444732965739290427392,
     295147905179352825856, 2361183241434822606848, 18889465931478580854784,
     37778931862957161709568, 75557863725914323419136, 151115727451828646838272]
  | 3 =>
    [1, 10, 12, 8, 24, 32, 64, 32768, 131072, 262144, 524288, 2048, 4096, 16777216, 33554432,
     128, 268435456, 256, 512, 1024, 1073741824, 2147483648, 4194304, 8589934592, 8192, 16384,
     67108864, 134217728, 65536, 536870912, 1048576, 2097152, 4398046511104, 8388608,
     17179869184, 34359738368, 68719476736, 137438953472, 562949953421312, 549755813888,
     1099511627776, 2199023255552, 4294967296, 8796093022208, 17592186044416, 18014398509481984,
     70368744177664, 72057594037927936, 281474976710656, 274877906944, 288230376151711744,
     2251799813685248, 576460752303423488, 9007199254740992, 35184372088832, 4611686018427387904,
     140737488355328, 9223372036854775808, 1125899906842624, 4503599627370496,
     73786976294838206464, 2305843009213693952, 36028797018963968, 144115188075855872,
     18446744073709551616, 36893488147419103232, 1152921504606846976, 147573952589676412928,
     295147905179352825856, 590295810358705651712, 1180591620717411303424,
     2361183241434822606848, 18889465931478580854784, 37778931862957161709568,
     4722366482869645213696, 9444732965739290427392, 75557863725914323419136,
     151115727451828646838272]
  | 4 =>
    [1, 2, 4, 24, 16, 48, 64, 128, 256, 524288, 1048576, 2097152, 4096, 8192, 16384, 134217728,
     65536, 536870912, 1073741824, 512, 1024, 2048, 4294967296, 8388608, 34359738368,
     137438953472, 274877906944, 32768, 1099511627776, 131072, 262144, 2147483648, 4194304,
     17592186044416, 35184372088832, 16777216, 140737488355328, 33554432, 67108864, 549755813888,
     268435456, 2199023255552, 4398046511104, 4503599627370496, 8589934592, 17179869184,
     70368744177664, 68719476736, 281474976710656, 562949953421312, 1125899906842624,
     2251799813685248, 8796093022208, 9007199254740992, 18014398509481984, 36028797018963968,
     72057594037927936, 144115188075855872, 18446744073709551616, 576460752303423488,
     1152921504606846976, 2305843009213693952, 295147905179352825856, 590295810358705651712,
     288230376151711744, 36893488147419103232, 2361183241434822606848, 4722366482869645213696,
     4611686018427387904, 9223372036854775808, 9444732965739290427392, 73786976294838206464,
     147573952589676412928, 1180591620717411303424, 18889465931478580854784,
     37778931862957161709568, 75557863725914323419136, 151115727451828646838272]
  | 5 =>
    [1, 2, 4, 8, 48, 32, 64, 128, 256, 512, 2097152, 4194304, 4096, 8192, 16384, 32768, 65536,
     131072, 262144, 2147483648, 4294967296, 1024, 2048, 8388608, 16777216, 33554432, 67108864,
     549755813888, 268435456, 2199023255552, 4398046511104, 524288, 1048576, 8589934592,
     17179869184, 70368744177664, 68719476736, 281474976710656, 1125899906842624, 134217728,
     2251799813685248, 536870912, 1073741824, 8796093022208, 9007199254740992, 36028797018963968,
     34359738368, 144115188075855872, 137438953472, 288230376151711744, 274877906944,
     1099511627776, 1152921504606846976, 17592186044416, 4611686018427387904, 35184372088832,
     9223372036854775808, 140737488355328, 562949953421312, 73786976294838206464,
     4503599627370496, 147573952589676412928, 18014398509481984, 72057594037927936,
     18446744073709551616, 1180591620717411303424, 576460752303423488, 2305843009213693952,
     295147905179352825856, 590295810358705651712, 36893488147419103232, 2361183241434822606848,
     4722366482869645213696, 9444732965739290427392, 18889465931478580854784,
     37778931862957161709568, 75557863725914323419136, 151115727451828646838272]

theorem eltBits_eq_xCols (i : Fin 6) : eltBits i = xCols i := by
  fin_cases i <;> decide +kernel

theorem nBits_eq_nCols (i : Fin 6) : nBits i = nCols i := by
  fin_cases i <;> decide +kernel

theorem slots_lt : ∀ n, slots n < 2 ^ (78 * n)
  | 0 => by simp [slots]
  | n + 1 => by
    have h := slots_lt n
    have h1 : 2 ^ (78 * n) * 2 ≤ 2 ^ (78 * (n + 1)) := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [slots]
    omega

theorem testBit_slots : ∀ n k : ℕ,
    (slots n).testBit k = (decide (k < 78 * n) && decide (k % 78 = 0))
  | 0, k => by simp [slots]
  | n + 1, k => by
    rw [slots, Nat.testBit_two_pow_mul_add _ (slots_lt n), testBit_slots n k]
    split_ifs with hk
    · rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    · rw [Bool.eq_iff_iff, Nat.testBit_one_eq_true_iff_self_eq_zero]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega

theorem mod_eq_of_spread {S : ℕ} (hS : ∀ k, S.testBit k = true → k % 78 = 0) :
    S % 2 ^ 78 = if S.testBit 0 then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · cases h : S.testBit 0 <;> simp
  · have h1 : (if S.testBit 0 then 1 else 0 : ℕ).testBit i = false := by
      split_ifs
      · exact Nat.testBit_lt_two_pow (by
          calc (1 : ℕ) < 2 ^ 1 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi)
      · simp
    rw [h1]
    by_cases h2 : i < 78
    · have h3 : S.testBit i = false := by
        by_contra h
        have := hS i (by simpa using h)
        omega
      simp [h3]
    · simp [h2]

theorem mul_eq_of_spread (a S : ℕ) :
    a * S = 2 ^ 78 * (a * (S / 2 ^ 78)) + a * (S % 2 ^ 78) := by
  conv_lhs => rw [← Nat.div_add_mod S (2 ^ 78)]
  ring

theorem testBit_mul_of_spread {a : ℕ} (ha : a < 2 ^ 78) {p : ℕ} (hp : p < 78) :
    ∀ (c : ℕ) {S : ℕ}, (∀ k, S.testBit k = true → k % 78 = 0) →
      (a * S).testBit (78 * c + p) = (S.testBit (78 * c) && a.testBit p) := by
  intro c
  induction c with
  | zero =>
    intro S hS
    have hlt : a * (S % 2 ^ 78) < 2 ^ 78 := by
      rw [mod_eq_of_spread hS]
      split_ifs <;> omega
    rw [mul_eq_of_spread, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_left (by omega),
      mod_eq_of_spread hS]
    simp only [Nat.mul_zero, Nat.zero_add]
    split_ifs with h <;> simp [h]
  | succ c ih =>
    intro S hS
    have hlt : a * (S % 2 ^ 78) < 2 ^ 78 := by
      rw [mod_eq_of_spread hS]
      split_ifs <;> omega
    have hS' : ∀ k, (S / 2 ^ 78).testBit k = true → k % 78 = 0 := by
      intro k hk
      rw [Nat.testBit_div_two_pow] at hk
      have := hS _ hk
      omega
    rw [mul_eq_of_spread, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_right (by omega),
      show 78 * (c + 1) + p - 78 = 78 * c + p by omega, ih hS', Nat.testBit_div_two_pow,
      show 78 * c + 78 = 78 * (c + 1) by ring]

theorem testBit_spread (B q k : ℕ) :
    (B / 2 ^ q &&& slots 78).testBit k =
      (B.testBit (k + q) && decide (k < 78 * 78) && decide (k % 78 = 0)) := by
  rw [Nat.testBit_land, Nat.testBit_div_two_pow, testBit_slots, Bool.and_assoc]

theorem spread_spec (B q : ℕ) :
    ∀ k, (B / 2 ^ q &&& slots 78).testBit k = true → k % 78 = 0 := by
  intro k hk
  rw [testBit_spread] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact hk.2

theorem col_lt (A q : ℕ) : col A q < 2 ^ 78 :=
  Nat.mod_lt _ (Nat.two_pow_pos 78)

theorem testBit_col (A q : ℕ) {p : ℕ} (hp : p < 78) :
    (col A q).testBit p = A.testBit (78 * q + p) := by
  rw [col, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true hp, Bool.true_and,
    Nat.add_comm]

theorem testBit_pack : ∀ (L : List ℕ) (c : ℕ) {p : ℕ}, p < 78 →
    (pack L).testBit (78 * c + p) = (L.getD c 0).testBit p
  | [], c, p, _ => by simp [pack]
  | a :: L, c, p, hp => by
    rw [pack, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt a (Nat.two_pow_pos 78))]
    rcases c with _ | c
    · rw [ite_eq_left (by omega), Nat.testBit_mod_two_pow]
      simp [hp]
    · rw [ite_eq_right (by omega), show 78 * (c + 1) + p - 78 = 78 * c + p by omega,
        testBit_pack L c hp]
      simp

variable (K : Type) [Field K]

def bitK (b : Bool) : K :=
  if b then 1 else 0

noncomputable def bitVec (m : ℕ) : RootModule Tag.E6 K :=
  ∑ p ∈ Finset.range 78, bitK K (m.testBit p) • posVec Tag.E6 K p

noncomputable def colVec (A c : ℕ) : RootModule Tag.E6 K :=
  ∑ p ∈ Finset.range 78, bitK K (A.testBit (78 * c + p)) • posVec Tag.E6 K p

noncomputable def toEnd
    (A : ℕ) : Module.End K (RootModule Tag.E6 K) :=
  ∑ c ∈ Finset.range 78, (posCoord Tag.E6 K c).smulRight (colVec K A c)

variable {K}

theorem dim_E6 : dim Tag.E6 = 78 :=
  rfl

theorem bitK_and (a b : Bool) : bitK K (a && b) = bitK K a * bitK K b := by
  cases a <;> cases b <;> simp [bitK]

theorem bitK_xor [CharP K 2] (a b : Bool) : bitK K (a ^^ b) = bitK K a + bitK K b := by
  cases a <;> cases b <;> simp [bitK, CharTwo.add_self_eq_zero]

theorem bitK_injective : Function.Injective (bitK K) := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitK]

theorem posCoord_sum_smul_posVec
    {p : ℕ} (hp : p < 78) (f : ℕ → K) :
    posCoord Tag.E6 K p (∑ q ∈ Finset.range 78, f q • posVec Tag.E6 K q) = f p := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · rw [posCoord_posVec (by rw [dim_E6]; exact hp), ite_eq_left rfl, mul_one]
  · intro q hq hqp
    rw [posCoord_posVec (by rw [dim_E6]; exact Finset.mem_range.1 hq), ite_eq_right (Ne.symm hqp),
      mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hp) h

theorem toEnd_apply
    (A : ℕ) (x : RootModule Tag.E6 K) :
    toEnd K A x = ∑ c ∈ Finset.range 78, posCoord Tag.E6 K c x • colVec K A c := by
  simp [toEnd]

theorem toEnd_posVec
    (A : ℕ) {c : ℕ} (hc : c < 78) :
    toEnd K A (posVec Tag.E6 K c) = colVec K A c := by
  rw [toEnd_apply, Finset.sum_eq_single c]
  · rw [posCoord_posVec (by rw [dim_E6]; exact hc), ite_eq_left rfl, one_smul]
  · intro q _ hqc
    rw [posCoord_posVec (by rw [dim_E6]; exact hc), ite_eq_right hqc, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.2 hc) h

theorem posCoord_toEnd_posVec
    (A : ℕ) {c p : ℕ} (hc : c < 78) (hp : p < 78) :
    posCoord Tag.E6 K p (toEnd K A (posVec Tag.E6 K c)) =
      bitK K (A.testBit (78 * c + p)) := by
  rw [toEnd_posVec A hc, colVec, posCoord_sum_smul_posVec hp]

theorem toEnd_sum_smul_posVec
    (A : ℕ) (f : ℕ → K) :
    toEnd K A (∑ q ∈ Finset.range 78, f q • posVec Tag.E6 K q) =
      ∑ q ∈ Finset.range 78, f q • colVec K A q := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [map_smul, toEnd_posVec A (Finset.mem_range.1 hq)]

theorem bitK_testBit_mulAux [CharP K 2] (A B : ℕ) {c p : ℕ} (hc : c < 78) (hp : p < 78) :
    ∀ n, bitK K ((mulAux A B n).testBit (78 * c + p)) =
      ∑ q ∈ Finset.range n, bitK K (A.testBit (78 * q + p)) * bitK K (B.testBit (78 * c + q))
  | 0 => by simp [mulAux, bitK]
  | n + 1 => by
    have hX : bitK K ((col A n * (B / 2 ^ n &&& slots 78)).testBit (78 * c + p)) =
        bitK K (A.testBit (78 * n + p)) * bitK K (B.testBit (78 * c + n)) := by
      rw [testBit_mul_of_spread (col_lt A n) hp c (spread_spec B n), testBit_spread,
        testBit_col A n hp]
      have h1 : decide (78 * c < 78 * 78) = true := decide_eq_true (by omega)
      have h2 : decide (78 * c % 78 = 0) = true := decide_eq_true (by omega)
      rw [h1, h2, Bool.and_true, Bool.and_true, bitK_and, mul_comm]
    rw [mulAux, Nat.testBit_xor, bitK_xor, hX, bitK_testBit_mulAux A B hc hp n,
      Finset.sum_range_succ]
    exact add_comm _ _

theorem toEnd_mul
    [CharP K 2] (A B : ℕ) : toEnd K (mul A B) = toEnd K A * toEnd K B := by
  refine ext_posVec fun c hc => ?_
  rw [dim_E6] at hc
  rw [Module.End.mul_apply, toEnd_posVec _ hc, toEnd_posVec _ hc, colVec, colVec,
    toEnd_sum_smul_posVec]
  calc ∑ p ∈ Finset.range 78, bitK K ((mul A B).testBit (78 * c + p)) • posVec Tag.E6 K p
      = ∑ p ∈ Finset.range 78, ∑ q ∈ Finset.range 78,
          (bitK K (B.testBit (78 * c + q)) * bitK K (A.testBit (78 * q + p))) •
            posVec Tag.E6 K p := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [mul, bitK_testBit_mulAux A B hc (Finset.mem_range.1 hp), Finset.sum_smul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [mul_comm]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [colVec, Finset.smul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [smul_smul]

theorem toEnd_eq_toEnd_iff (A B : ℕ) :
    toEnd K A = toEnd K B ↔ A % 2 ^ 6084 = B % 2 ^ 6084 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hk : k < 6084
    · have hc : k / 78 < 78 := by omega
      have hp : k % 78 < 78 := by omega
      have e : k = 78 * (k / 78) + k % 78 := (Nat.div_add_mod k 78).symm
      have h1 := congrArg
        (fun f => posCoord Tag.E6 K (k % 78) (f (posVec Tag.E6 K (k / 78)))) h
      simp only [posCoord_toEnd_posVec _ hc hp] at h1
      rw [e, bitK_injective h1]
    · simp [hk]
  · intro h
    have hbit : ∀ k, k < 6084 → A.testBit k = B.testBit k := by
      intro k hk
      have h1 := congrArg (fun n => n.testBit k) h
      simp only [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and] at h1
      exact h1
    have hcol : ∀ c, c < 78 → colVec K A c = colVec K B c := by
      intro c hc
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hbit _ (by have := Finset.mem_range.1 hp; omega)]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [hcol c (Finset.mem_range.1 hc)]

theorem colVec_pack (L : List ℕ) (c : ℕ) : colVec K (pack L) c = bitVec K (L.getD c 0) :=
  Finset.sum_congr rfl fun p hp => by rw [testBit_pack L c (Finset.mem_range.1 hp)]

theorem bitVec_zero : bitVec K 0 = 0 := by
  simp [bitVec, bitK]

theorem bitVec_xor [CharP K 2] (m n : ℕ) : bitVec K (m ^^^ n) = bitVec K m + bitVec K n := by
  rw [bitVec, bitVec, bitVec, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Nat.testBit_xor, bitK_xor, add_smul]

theorem bitVec_two_pow
    {p : ℕ} (hp : p < 78) : bitVec K (2 ^ p) = posVec Tag.E6 K p := by
  rw [bitVec, Finset.sum_eq_single p]
  · simp [bitK]
  · intro q _ hqp
    simp [bitK, Ne.symm hqp]
  · intro h
    exact absurd (Finset.mem_range.2 hp) h

theorem intCast_eq_of_charTwo [CharP K 2] (z : ℤ) :
    (z : K) = if z % 2 = 0 then 0 else 1 := by
  split_ifs with h
  · exact (CharP.intCast_eq_zero_iff K 2 z).2 (Int.dvd_of_emod_eq_zero h)
  · have h1 : z % 2 = 1 := by omega
    have h2 : z = 2 * (z / 2) + 1 := by omega
    rw [h2]
    push_cast
    rw [CharTwo.two_eq_zero, zero_mul, zero_add]

theorem maskOf_cons (x : ℕ × ℤ) (v : List (ℕ × ℤ)) :
    maskOf (x :: v) = if x.2 % 2 = 0 then maskOf v else maskOf v ^^^ 2 ^ x.1 :=
  rfl

theorem vecOf_eq_bitVec [CharP K 2] :
    ∀ v : List (ℕ × ℤ), ValidVec Tag.E6 v → vecOf Tag.E6 K v = bitVec K (maskOf v)
  | [], _ => by rw [vecOf_nil, maskOf, List.foldr_nil, bitVec_zero]
  | x :: v, hv => by
    have hx : x.1 < 78 := hv x (List.mem_cons_self ..)
    have ih := vecOf_eq_bitVec v fun y hy => hv y (List.mem_cons_of_mem _ hy)
    rw [vecOf_cons, ih, maskOf_cons, intCast_eq_of_charTwo]
    split_ifs with h
    · rw [zero_smul, zero_add]
    · rw [one_smul, bitVec_xor, bitVec_two_pow hx, add_comm]

theorem getD_map_range {f : ℕ → ℕ} {c : ℕ} (hc : c < 78) :
    ((List.range 78).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

variable (K) in
theorem toEnd_pack_posVec
    (L : List ℕ) {c : ℕ} (hc : c < 78) :
    toEnd K (pack L) (posVec Tag.E6 K c) = bitVec K (L.getD c 0) := by
  rw [toEnd_posVec _ hc, colVec_pack]

theorem toEnd_pack_nBits
    [CharP K 2] (i : Fin 6) :
    toEnd K (pack (nBits i)) =
      (weylElt Tag.E6 K (idx i) 1 : Module.End K (RootModule Tag.E6 K)) := by
  refine ext_posVec fun c hc => ?_
  rw [dim_E6] at hc
  have hc' : c < dim Tag.E6 := by rw [dim_E6]; exact hc
  rw [toEnd_pack_posVec K _ hc, nBits, getD_map_range hc,
    weylElt_posVec (idx i) hc', vecOf_eq_bitVec _ (validVec_nPos (idx i) hc')]

theorem elt_one_posVec
    (α : Root Tag.E6) {c : ℕ} (hc : c < 78) :
    (rootOperatorFamily Tag.E6).elt K α 1 (posVec Tag.E6 K c) =
      vecOf Tag.E6 K ((c, 1) :: (colOf (entries Tag.E6 (rootPos α) 1) c ++
        colOf (entries Tag.E6 (rootPos α) 2) c ++
          colOf (entries Tag.E6 (rootPos α) 3) c)) := by
  have hc' : c < dim Tag.E6 := by rw [dim_E6]; exact hc
  change (∑ k ∈ Finset.range 4, (1 : K) ^ k • dataD Tag.E6 K α k)
    (posVec Tag.E6 K c) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, one_pow, one_smul, zero_add,
    LinearMap.add_apply, dataD]
  simp only [ite_true, show (1 : ℕ) ≠ 0 by decide,
    show (2 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 0 by decide, ite_false,
    show (1 : ℕ) ≤ 3 by decide, show (2 : ℕ) ≤ 3 by decide, le_refl, Module.End.one_apply,
    entriesOp_posVec _ hc', vecOf_cons, vecOf_append, Int.cast_one, one_smul, add_assoc]

theorem toEnd_pack_eltBits
    [CharP K 2] (α : Root Tag.E6) :
    toEnd K (pack (eltBits (rootPos α))) = (rootOperatorFamily Tag.E6).elt K α 1 := by
  refine ext_posVec fun c hc => ?_
  rw [dim_E6] at hc
  rw [toEnd_pack_posVec K _ hc, eltBits, getD_map_range hc, elt_one_posVec α hc]
  symm
  refine vecOf_eq_bitVec _ fun x hx => ?_
  rcases List.mem_cons.1 hx with rfl | hx
  · rw [dim_E6]; exact hc
  have hval : ∀ k ∈ [1, 2, 3],
      ValidVec Tag.E6 (colOf (entries Tag.E6 (rootPos α) k) c) := fun k hk =>
    (validEntries_of_validB
      (validB_of_allValid (τ := Tag.E6) e6_allValid (rootPos_lt α) hk)).colOf c
  simp only [List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact hval 1 (by simp) x hx
  · exact hval 2 (by simp) x hx
  · exact hval 3 (by simp) x hx

theorem toEnd_oneBits
    : toEnd K oneBits = 1 := by
  refine ext_posVec fun c hc => ?_
  rw [dim_E6] at hc
  rw [oneBits, toEnd_pack_posVec K _ hc, getD_map_range hc, bitVec_two_pow hc,
    Module.End.one_apply]

variable (K) in
@[expose] def HasBits
    (g : adjointGroup Tag.E6 K) (A : ℕ) : Prop :=
  ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) = toEnd K A

theorem HasBits.mul
    [CharP K 2] {g h : adjointGroup Tag.E6 K} {A B : ℕ} (hg : HasBits K g A)
    (hh : HasBits K h B) : HasBits K (g * h) (mul A B) := by
  rw [HasBits, toEnd_mul, ← hg, ← hh]
  rfl

theorem HasBits.eq_iff
    {g h : adjointGroup Tag.E6 K} {A B : ℕ} (hg : HasBits K g A)
    (hh : HasBits K h B) : g = h ↔ A % 2 ^ 6084 = B % 2 ^ 6084 := by
  rw [← toEnd_eq_toEnd_iff (K := K), ← hg, ← hh]
  exact ⟨fun e => by rw [e], fun e => Subtype.ext (Units.ext e)⟩

theorem hasBits_one
    : HasBits K 1 oneBits :=
  toEnd_oneBits.symm

theorem hasBits_eltElement
    [CharP K 2] (α : Root Tag.E6) :
    HasBits K ((rootOperatorFamily Tag.E6).eltElement α 1) (pack (eltBits (rootPos α))) :=
  (toEnd_pack_eltBits α).symm

inductive Letter
  | x (i : Fin 6)
  | n (i : Fin 6)

namespace Letter

@[expose] def bits : Letter → ℕ
  | x i => pack (xCols i)
  | n i => pack (nCols i)

variable (K) in
@[expose] noncomputable def elt
    : Letter → adjointGroup Tag.E6 K
  | x i => xElement (idx i) 1
  | n i => weylElement Tag.E6 K (idx i)

theorem hasBits
    [CharP K 2] : ∀ l : Letter, HasBits K (l.elt K) l.bits
  | x i => by
    have h := toEnd_pack_eltBits (K := K) (simpleRoot Tag.E6 (idx i))
    rw [rootPos_simpleRoot, show ((idx i : Fin Tag.E6.rank) : ℕ) = i from rfl] at h
    rw [HasBits, bits, ← eltBits_eq_xCols, h, (rootOperatorFamily Tag.E6).elt_simple]
    rfl
  | n i => by
    rw [HasBits, bits, ← nBits_eq_nCols, toEnd_pack_nBits]
    rfl

theorem elt_mul_self
    [CharP K 2] : ∀ l : Letter, l.elt K * l.elt K = 1
  | x i => by
    rw [elt, ← xElement_add, CharTwo.add_self_eq_zero, xElement_zero]
  | n i => by
    have hu : (-1 : Kˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
    have h : (weylElement Tag.E6 K (idx i))⁻¹ = weylElement Tag.E6 K (idx i) :=
      Subtype.ext (by
        change (weylElt Tag.E6 K (idx i) 1)⁻¹ = weylElt Tag.E6 K (idx i) 1
        rw [weylElt_inv, hu])
    rw [elt]
    nth_rw 1 [← h]
    exact inv_mul_cancel _

theorem elt_inv
    [CharP K 2] (l : Letter) : (l.elt K)⁻¹ = l.elt K :=
  inv_eq_of_mul_eq_one_right (l.elt_mul_self)

end Letter

@[expose] def evalB (w : List Letter) : ℕ :=
  w.foldr (fun l M => mul l.bits M) oneBits

variable (K) in
@[expose] noncomputable def evalG
    (w : List Letter) : adjointGroup Tag.E6 K :=
  (w.map (Letter.elt K)).prod

@[simp] theorem evalG_nil
    : evalG K [] = 1 :=
  rfl

@[simp] theorem evalG_cons
    (l : Letter) (w : List Letter) :
    evalG K (l :: w) = l.elt K * evalG K w := by
  simp [evalG]

theorem evalG_append
    (w w' : List Letter) : evalG K (w ++ w') = evalG K w * evalG K w' := by
  simp [evalG]

theorem evalG_singleton
    (l : Letter) : evalG K [l] = l.elt K := by
  simp

theorem evalG_inv
    [CharP K 2] : ∀ w : List Letter, (evalG K w)⁻¹ = evalG K w.reverse
  | [] => by simp
  | l :: w => by
    rw [evalG_cons, mul_inv_rev, evalG_inv w, Letter.elt_inv, List.reverse_cons, evalG_append,
      evalG_singleton]

theorem hasBits_evalG
    [CharP K 2] : ∀ w : List Letter, HasBits K (evalG K w) (evalB w)
  | [] => hasBits_one
  | l :: w => by
    rw [evalG_cons]
    exact l.hasBits.mul (hasBits_evalG w)

theorem evalG_eq_evalG_iff
    [CharP K 2] (w w' : List Letter) :
    evalG K w = evalG K w' ↔ evalB w % 2 ^ 6084 = evalB w' % 2 ^ 6084 :=
  (hasBits_evalG w).eq_iff (hasBits_evalG w')

theorem eltElement_eq_evalG_iff
    [CharP K 2] (α : Root Tag.E6) (w : List Letter) :
    (rootOperatorFamily Tag.E6).eltElement α 1 = evalG K w ↔
      pack (eltBits (rootPos α)) % 2 ^ 6084 = evalB w % 2 ^ 6084 :=
  (hasBits_eltElement α).eq_iff (hasBits_evalG w)

end CFSG.LieType.SeitzGeneration.ExcHighThree.E6Bits
