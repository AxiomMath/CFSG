module

public import CFSG.LieType.Chevalley.RootConj
public import CFSG.LieType.Ree.Duality

public section

namespace CFSG.LieType.Simplicity.TitsBits

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree

@[expose] def col (A q : ℕ) : ℕ :=
  A / 2 ^ (52 * q) % 2 ^ 52

@[expose] def slots : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ (52 * n) * 1 + slots n

@[expose] def mulAux (A B : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (col A n * (B / 2 ^ n &&& slots 52)) ^^^ mulAux A B n

@[expose] def mul (A B : ℕ) : ℕ :=
  mulAux A B 52

@[expose] def pack : List ℕ → ℕ
  | [] => 0
  | a :: L => 2 ^ 52 * pack L + a % 2 ^ 52

@[expose] def maskOf (v : List (ℕ × ℤ)) : ℕ :=
  v.foldr (fun x m => if x.2 % 2 = 0 then m else m ^^^ 2 ^ x.1) 0

@[expose] def eltBits (a : ℕ) : List ℕ :=
  (List.range 52).map fun c => maskOf ((c, 1) :: (colOf (entries ReeTag.F4.tag a 1) c ++
    colOf (entries ReeTag.F4.tag a 2) c ++ colOf (entries ReeTag.F4.tag a 3) c))

abbrev idx (i : Fin 4) : Fin ReeTag.F4.tag.rank :=
  Fin.cast rfl i

@[expose] def nBits (i : Fin 4) : List ℕ :=
  (List.range 52).map fun p => maskOf (nPos ReeTag.F4.tag (idx i) p)

@[expose] def oneBits : ℕ :=
  pack ((List.range 52).map (2 ^ ·))

@[expose] def xCols : Fin 4 → List ℕ
  | 0 =>
    [1, 18, 4, 8, 16, 544, 64, 128, 273, 512, 1024, 133120, 1052672, 8192, 16384, 32768, 66560,
      131072, 262144, 67633152, 1048576, 270532608, 4194304, 8388608, 17039360, 33554432, 67108864,
      134217728, 268435456, 34896609280, 1077936128, 2147483648, 4294967296, 8724152320,
      17179869184, 34359738368, 70866960384, 137438953472, 274877906944, 549755813888,
      1099511627776, 2336462209024, 4398046511104, 149533581377536, 17592186044416, 35184372088832,
      70368744177664, 140737488355328, 281474976710656, 562949953421312, 1196268651020288,
      2251799813685248]
  | 1 =>
    [33, 2, 4, 8, 528, 32, 4160, 128, 256, 512, 1058, 2048, 4096, 8192, 2113536, 32768, 65792,
      33685504, 262144, 524288, 1048576, 2097152, 4202496, 8388608, 16777216, 33554432,
      17246978048, 134217728, 268435456, 536870912, 1073741824, 2155872256, 4311744512, 8589934592,
      17179869184, 1133871366144, 68719476736, 137438953472, 283467841536, 9345848836096,
      1099511627776, 2199023255552, 4398046511104, 8796093022208, 17592186044416, 37383395344384,
      74766790688768, 140737488355328, 281474976710656, 562949953421312, 1125899906842624,
      2251799813685248]
  | 2 =>
    [1, 66, 4, 72, 16, 6176, 64, 16512, 256, 1180160, 1024, 2048, 4096, 8260, 16384, 32768, 65536,
      131072, 4457472, 524288, 1048576, 538968064, 4194304, 8421376, 1090584576, 33554432,
      67108864, 134217728, 34628173824, 536870912, 1073741824, 2147483648, 4294967296, 8589934592,
      282041912393728, 34359738368, 68719476736, 139586437120, 274877906944, 549755813888,
      18691697672192, 2267742732288, 2256472738103296, 8796093022208, 17592186044416,
      35184372088832, 70368744177664, 140737488355328, 281474976710656, 598134325510144,
      1125899906842624, 2251799813685248]
  | 3 =>
    [1, 2, 132, 8, 16, 32, 16448, 128, 256, 512, 1024, 537397248, 2101248, 8192, 16384, 32904,
      65536, 34426978304, 262144, 524288, 269484032, 2097152, 4194304, 8396800, 16777216,
      1116725051392, 67108864, 137573433344, 268435456, 536870912, 1073741824, 2151677952,
      4294967296, 2207629967360, 17179869184, 34359738368, 69793218560, 137438953472,
      35463544963072, 549755813888, 1099511627776, 2199023255552, 4398046511104, 8796093022208,
      299067162755072, 35184372088832, 70368744177664, 140737488355328, 281474976710656,
      562949953421312, 1125899906842624, 2814749767106560]

@[expose] def nCols : Fin 4 → List ℕ
  | 0 =>
    [1, 3, 4, 8, 256, 512, 64, 128, 16, 32, 65536, 131072, 1048576, 8192, 16384, 32768, 1024, 2048,
      16777216, 67108864, 4096, 268435456, 1073741824, 8388608, 262144, 33554432, 524288,
      8589934592, 2097152, 34359738368, 4194304, 68719476736, 4294967296, 134217728, 17179869184,
      536870912, 2147483648, 2199023255552, 274877906944, 549755813888, 1099511627776,
      137438953472, 4398046511104, 140737488355328, 17592186044416, 35184372088832,
      1125899906842624, 8796093022208, 281474976710656, 562949953421312, 70368744177664,
      2251799813685248]
  | 1 =>
    [3, 2, 4, 8, 512, 1024, 4096, 128, 65536, 16, 32, 2048, 64, 4194304, 2097152, 32768, 256,
      33554432, 262144, 524288, 1048576, 16384, 8192, 2147483648, 4294967296, 131072, 17179869184,
      134217728, 268435456, 536870912, 1073741824, 8388608, 16777216, 274877906944, 67108864,
      1099511627776, 68719476736, 137438953472, 8589934592, 8796093022208, 34359738368,
      35184372088832, 70368744177664, 549755813888, 17592186044416, 2199023255552, 4398046511104,
      140737488355328, 281474976710656, 562949953421312, 1125899906842624, 2251799813685248]
  | 2 =>
    [1, 6, 4, 12, 16, 2048, 8192, 16384, 256, 131072, 262144, 32, 4096, 64, 128, 8388608, 16777216,
      512, 1024, 524288, 1048576, 536870912, 4194304, 32768, 65536, 33554432, 67108864, 134217728,
      34359738368, 2097152, 1073741824, 137438953472, 4294967296, 8589934592, 549755813888,
      268435456, 2199023255552, 2147483648, 4398046511104, 17179869184, 17592186044416,
      68719476736, 274877906944, 8796093022208, 1099511627776, 562949953421312, 70368744177664,
      140737488355328, 281474976710656, 35184372088832, 1125899906842624, 2251799813685248]
  | 3 =>
    [1, 2, 12, 8, 16, 32, 16384, 32768, 256, 512, 1024, 524288, 2097152, 8388608, 64, 128, 65536,
      67108864, 134217728, 2048, 268435456, 4096, 2147483648, 8192, 8589934592, 17179869184,
      131072, 262144, 1048576, 536870912, 68719476736, 4194304, 274877906944, 16777216, 33554432,
      34359738368, 1073741824, 137438953472, 4294967296, 549755813888, 1099511627776,
      2199023255552, 4398046511104, 8796093022208, 281474976710656, 35184372088832, 70368744177664,
      140737488355328, 17592186044416, 2251799813685248, 1125899906842624, 562949953421312]

theorem eltBits_eq_xCols (i : Fin 4) : eltBits i = xCols i := by
  fin_cases i <;> decide +kernel

theorem nBits_eq_nCols (i : Fin 4) : nBits i = nCols i := by
  fin_cases i <;> decide +kernel

theorem slots_lt : ∀ n, slots n < 2 ^ (52 * n)
  | 0 => by simp [slots]
  | n + 1 => by
    have h := slots_lt n
    have h1 : 2 ^ (52 * n) * 2 ≤ 2 ^ (52 * (n + 1)) := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [slots]
    omega

theorem testBit_slots : ∀ n k : ℕ,
    (slots n).testBit k = (decide (k < 52 * n) && decide (k % 52 = 0))
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

theorem mod_eq_of_spread {S : ℕ} (hS : ∀ k, S.testBit k = true → k % 52 = 0) :
    S % 2 ^ 52 = if S.testBit 0 then 1 else 0 := by
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
    by_cases h2 : i < 52
    · have h3 : S.testBit i = false := by
        by_contra h
        have := hS i (by simpa using h)
        omega
      simp [h3]
    · simp [h2]

theorem mul_eq_of_spread (a S : ℕ) :
    a * S = 2 ^ 52 * (a * (S / 2 ^ 52)) + a * (S % 2 ^ 52) := by
  conv_lhs => rw [← Nat.div_add_mod S (2 ^ 52)]
  ring

theorem testBit_mul_of_spread {a : ℕ} (ha : a < 2 ^ 52) {p : ℕ} (hp : p < 52) :
    ∀ (c : ℕ) {S : ℕ}, (∀ k, S.testBit k = true → k % 52 = 0) →
      (a * S).testBit (52 * c + p) = (S.testBit (52 * c) && a.testBit p) := by
  intro c
  induction c with
  | zero =>
    intro S hS
    have hlt : a * (S % 2 ^ 52) < 2 ^ 52 := by
      rw [mod_eq_of_spread hS]
      split_ifs <;> omega
    rw [mul_eq_of_spread, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_left (by omega),
      mod_eq_of_spread hS]
    simp only [Nat.mul_zero, Nat.zero_add]
    split_ifs with h <;> simp [h]
  | succ c ih =>
    intro S hS
    have hlt : a * (S % 2 ^ 52) < 2 ^ 52 := by
      rw [mod_eq_of_spread hS]
      split_ifs <;> omega
    have hS' : ∀ k, (S / 2 ^ 52).testBit k = true → k % 52 = 0 := by
      intro k hk
      rw [Nat.testBit_div_two_pow] at hk
      have := hS _ hk
      omega
    rw [mul_eq_of_spread, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_right (by omega),
      show 52 * (c + 1) + p - 52 = 52 * c + p by omega, ih hS', Nat.testBit_div_two_pow,
      show 52 * c + 52 = 52 * (c + 1) by ring]

theorem testBit_spread (B q k : ℕ) :
    (B / 2 ^ q &&& slots 52).testBit k =
      (B.testBit (k + q) && decide (k < 52 * 52) && decide (k % 52 = 0)) := by
  rw [Nat.testBit_land, Nat.testBit_div_two_pow, testBit_slots, Bool.and_assoc]

theorem spread_spec (B q : ℕ) :
    ∀ k, (B / 2 ^ q &&& slots 52).testBit k = true → k % 52 = 0 := by
  intro k hk
  rw [testBit_spread] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact hk.2

theorem col_lt (A q : ℕ) : col A q < 2 ^ 52 :=
  Nat.mod_lt _ (Nat.two_pow_pos 52)

theorem testBit_col (A q : ℕ) {p : ℕ} (hp : p < 52) :
    (col A q).testBit p = A.testBit (52 * q + p) := by
  rw [col, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true hp, Bool.true_and,
    Nat.add_comm]

theorem testBit_pack : ∀ (L : List ℕ) (c : ℕ) {p : ℕ}, p < 52 →
    (pack L).testBit (52 * c + p) = (L.getD c 0).testBit p
  | [], c, p, _ => by simp [pack]
  | a :: L, c, p, hp => by
    rw [pack, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt a (Nat.two_pow_pos 52))]
    rcases c with _ | c
    · rw [ite_eq_left (by omega), Nat.testBit_mod_two_pow]
      simp [hp]
    · rw [ite_eq_right (by omega), show 52 * (c + 1) + p - 52 = 52 * c + p by omega,
        testBit_pack L c hp]
      simp

variable (K : Type) [Field K]

def bitK (b : Bool) : K :=
  if b then 1 else 0

noncomputable def bitVec (m : ℕ) : RootModule ReeTag.F4.tag K :=
  ∑ p ∈ Finset.range 52, bitK K (m.testBit p) • posVec ReeTag.F4.tag K p

noncomputable def colVec (A c : ℕ) : RootModule ReeTag.F4.tag K :=
  ∑ p ∈ Finset.range 52, bitK K (A.testBit (52 * c + p)) • posVec ReeTag.F4.tag K p

noncomputable def toEnd
    (A : ℕ) : Module.End K (RootModule ReeTag.F4.tag K) :=
  ∑ c ∈ Finset.range 52, (posCoord ReeTag.F4.tag K c).smulRight (colVec K A c)

variable {K}

theorem dim_F4 : dim ReeTag.F4.tag = 52 :=
  rfl

theorem bitK_and (a b : Bool) : bitK K (a && b) = bitK K a * bitK K b := by
  cases a <;> cases b <;> simp [bitK]

theorem bitK_xor [CharP K 2] (a b : Bool) : bitK K (a ^^ b) = bitK K a + bitK K b := by
  cases a <;> cases b <;> simp [bitK, CharTwo.add_self_eq_zero]

theorem bitK_injective : Function.Injective (bitK K) := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitK]

theorem posCoord_sum_smul_posVec
    {p : ℕ} (hp : p < 52) (f : ℕ → K) :
    posCoord ReeTag.F4.tag K p (∑ q ∈ Finset.range 52, f q • posVec ReeTag.F4.tag K q) = f p := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · rw [posCoord_posVec (by rw [dim_F4]; exact hp), ite_eq_left rfl, mul_one]
  · intro q hq hqp
    rw [posCoord_posVec (by rw [dim_F4]; exact Finset.mem_range.1 hq), ite_eq_right (Ne.symm hqp),
      mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hp) h

theorem toEnd_apply
    (A : ℕ) (x : RootModule ReeTag.F4.tag K) :
    toEnd K A x = ∑ c ∈ Finset.range 52, posCoord ReeTag.F4.tag K c x • colVec K A c := by
  simp [toEnd]

theorem toEnd_posVec
    (A : ℕ) {c : ℕ} (hc : c < 52) :
    toEnd K A (posVec ReeTag.F4.tag K c) = colVec K A c := by
  rw [toEnd_apply, Finset.sum_eq_single c]
  · rw [posCoord_posVec (by rw [dim_F4]; exact hc), ite_eq_left rfl, one_smul]
  · intro q _ hqc
    rw [posCoord_posVec (by rw [dim_F4]; exact hc), ite_eq_right hqc, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.2 hc) h

theorem posCoord_toEnd_posVec
    (A : ℕ) {c p : ℕ} (hc : c < 52) (hp : p < 52) :
    posCoord ReeTag.F4.tag K p (toEnd K A (posVec ReeTag.F4.tag K c)) =
      bitK K (A.testBit (52 * c + p)) := by
  rw [toEnd_posVec A hc, colVec, posCoord_sum_smul_posVec hp]

theorem toEnd_sum_smul_posVec
    (A : ℕ) (f : ℕ → K) :
    toEnd K A (∑ q ∈ Finset.range 52, f q • posVec ReeTag.F4.tag K q) =
      ∑ q ∈ Finset.range 52, f q • colVec K A q := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [map_smul, toEnd_posVec A (Finset.mem_range.1 hq)]

theorem bitK_testBit_mulAux [CharP K 2] (A B : ℕ) {c p : ℕ} (hc : c < 52) (hp : p < 52) :
    ∀ n, bitK K ((mulAux A B n).testBit (52 * c + p)) =
      ∑ q ∈ Finset.range n, bitK K (A.testBit (52 * q + p)) * bitK K (B.testBit (52 * c + q))
  | 0 => by simp [mulAux, bitK]
  | n + 1 => by
    have hX : bitK K ((col A n * (B / 2 ^ n &&& slots 52)).testBit (52 * c + p)) =
        bitK K (A.testBit (52 * n + p)) * bitK K (B.testBit (52 * c + n)) := by
      rw [testBit_mul_of_spread (col_lt A n) hp c (spread_spec B n), testBit_spread,
        testBit_col A n hp]
      have h1 : decide (52 * c < 52 * 52) = true := decide_eq_true (by omega)
      have h2 : decide (52 * c % 52 = 0) = true := decide_eq_true (by omega)
      rw [h1, h2, Bool.and_true, Bool.and_true, bitK_and, mul_comm]
    rw [mulAux, Nat.testBit_xor, bitK_xor, hX, bitK_testBit_mulAux A B hc hp n,
      Finset.sum_range_succ]
    exact add_comm _ _

theorem toEnd_mul
    [CharP K 2] (A B : ℕ) : toEnd K (mul A B) = toEnd K A * toEnd K B := by
  refine ext_posVec fun c hc => ?_
  rw [dim_F4] at hc
  rw [Module.End.mul_apply, toEnd_posVec _ hc, toEnd_posVec _ hc, colVec, colVec,
    toEnd_sum_smul_posVec]
  calc ∑ p ∈ Finset.range 52, bitK K ((mul A B).testBit (52 * c + p)) • posVec ReeTag.F4.tag K p
      = ∑ p ∈ Finset.range 52, ∑ q ∈ Finset.range 52,
          (bitK K (B.testBit (52 * c + q)) * bitK K (A.testBit (52 * q + p))) •
            posVec ReeTag.F4.tag K p := by
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
    toEnd K A = toEnd K B ↔ A % 2 ^ 2704 = B % 2 ^ 2704 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hk : k < 2704
    · have hc : k / 52 < 52 := by omega
      have hp : k % 52 < 52 := by omega
      have e : k = 52 * (k / 52) + k % 52 := (Nat.div_add_mod k 52).symm
      have h1 := congrArg
        (fun f => posCoord ReeTag.F4.tag K (k % 52) (f (posVec ReeTag.F4.tag K (k / 52)))) h
      simp only [posCoord_toEnd_posVec _ hc hp] at h1
      rw [e, bitK_injective h1]
    · simp [hk]
  · intro h
    have hbit : ∀ k, k < 2704 → A.testBit k = B.testBit k := by
      intro k hk
      have h1 := congrArg (fun n => n.testBit k) h
      simp only [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and] at h1
      exact h1
    have hcol : ∀ c, c < 52 → colVec K A c = colVec K B c := by
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
    {p : ℕ} (hp : p < 52) : bitVec K (2 ^ p) = posVec ReeTag.F4.tag K p := by
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
    ∀ v : List (ℕ × ℤ), ValidVec ReeTag.F4.tag v → vecOf ReeTag.F4.tag K v = bitVec K (maskOf v)
  | [], _ => by rw [vecOf_nil, maskOf, List.foldr_nil, bitVec_zero]
  | x :: v, hv => by
    have hx : x.1 < 52 := hv x (List.mem_cons_self ..)
    have ih := vecOf_eq_bitVec v fun y hy => hv y (List.mem_cons_of_mem _ hy)
    rw [vecOf_cons, ih, maskOf_cons, intCast_eq_of_charTwo]
    split_ifs with h
    · rw [zero_smul, zero_add]
    · rw [one_smul, bitVec_xor, bitVec_two_pow hx, add_comm]

theorem getD_map_range {f : ℕ → ℕ} {c : ℕ} (hc : c < 52) :
    ((List.range 52).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

variable (K) in
theorem toEnd_pack_posVec
    (L : List ℕ) {c : ℕ} (hc : c < 52) :
    toEnd K (pack L) (posVec ReeTag.F4.tag K c) = bitVec K (L.getD c 0) := by
  rw [toEnd_posVec _ hc, colVec_pack]

theorem toEnd_pack_nBits
    [CharP K 2] (i : Fin 4) :
    toEnd K (pack (nBits i)) =
      (weylElt ReeTag.F4.tag K (idx i) 1 : Module.End K (RootModule ReeTag.F4.tag K)) := by
  refine ext_posVec fun c hc => ?_
  rw [dim_F4] at hc
  have hc' : c < dim ReeTag.F4.tag := by rw [dim_F4]; exact hc
  rw [toEnd_pack_posVec K _ hc, nBits, getD_map_range hc,
    weylElt_posVec (idx i) hc', vecOf_eq_bitVec _ (validVec_nPos (idx i) hc')]

theorem elt_one_posVec
    (α : Root ReeTag.F4.tag) {c : ℕ} (hc : c < 52) :
    (rootOperatorFamily ReeTag.F4.tag).elt K α 1 (posVec ReeTag.F4.tag K c) =
      vecOf ReeTag.F4.tag K ((c, 1) :: (colOf (entries ReeTag.F4.tag (rootPos α) 1) c ++
        colOf (entries ReeTag.F4.tag (rootPos α) 2) c ++
          colOf (entries ReeTag.F4.tag (rootPos α) 3) c)) := by
  have hc' : c < dim ReeTag.F4.tag := by rw [dim_F4]; exact hc
  change (∑ k ∈ Finset.range 4, (1 : K) ^ k • dataD ReeTag.F4.tag K α k)
    (posVec ReeTag.F4.tag K c) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, one_pow, one_smul, zero_add,
    LinearMap.add_apply, dataD]
  simp only [ite_true, show (1 : ℕ) ≠ 0 by decide,
    show (2 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 0 by decide, ite_false,
    show (1 : ℕ) ≤ 3 by decide, show (2 : ℕ) ≤ 3 by decide, le_refl, Module.End.one_apply,
    entriesOp_posVec _ hc', vecOf_cons, vecOf_append, Int.cast_one, one_smul, add_assoc]

theorem toEnd_pack_eltBits
    [CharP K 2] (α : Root ReeTag.F4.tag) :
    toEnd K (pack (eltBits (rootPos α))) = (rootOperatorFamily ReeTag.F4.tag).elt K α 1 := by
  refine ext_posVec fun c hc => ?_
  rw [dim_F4] at hc
  rw [toEnd_pack_posVec K _ hc, eltBits, getD_map_range hc, elt_one_posVec α hc]
  symm
  refine vecOf_eq_bitVec _ fun x hx => ?_
  rcases List.mem_cons.1 hx with rfl | hx
  · rw [dim_F4]; exact hc
  have hval : ∀ k ∈ [1, 2, 3],
      ValidVec ReeTag.F4.tag (colOf (entries ReeTag.F4.tag (rootPos α) k) c) := fun k hk =>
    (validEntries_of_validB
      (validB_of_allValid (τ := ReeTag.F4.tag) f4_allValid (rootPos_lt α) hk)).colOf c
  simp only [List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact hval 1 (by simp) x hx
  · exact hval 2 (by simp) x hx
  · exact hval 3 (by simp) x hx

theorem toEnd_oneBits
    : toEnd K oneBits = 1 := by
  refine ext_posVec fun c hc => ?_
  rw [dim_F4] at hc
  rw [oneBits, toEnd_pack_posVec K _ hc, getD_map_range hc, bitVec_two_pow hc,
    Module.End.one_apply]

variable (K) in
def HasBits
    (g : adjointGroup ReeTag.F4.tag K) (A : ℕ) : Prop :=
  ((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) = toEnd K A

theorem HasBits.mul
    [CharP K 2] {g h : adjointGroup ReeTag.F4.tag K} {A B : ℕ} (hg : HasBits K g A)
    (hh : HasBits K h B) : HasBits K (g * h) (mul A B) := by
  rw [HasBits, toEnd_mul, ← hg, ← hh]
  rfl

theorem HasBits.eq_iff
    {g h : adjointGroup ReeTag.F4.tag K} {A B : ℕ} (hg : HasBits K g A)
    (hh : HasBits K h B) : g = h ↔ A % 2 ^ 2704 = B % 2 ^ 2704 := by
  rw [← toEnd_eq_toEnd_iff (K := K), ← hg, ← hh]
  exact ⟨fun e => by rw [e], fun e => Subtype.ext (Units.ext e)⟩

theorem hasBits_one
    : HasBits K 1 oneBits :=
  toEnd_oneBits.symm

theorem hasBits_eltElement
    [CharP K 2] (α : Root ReeTag.F4.tag) :
    HasBits K ((rootOperatorFamily ReeTag.F4.tag).eltElement α 1) (pack (eltBits (rootPos α))) :=
  (toEnd_pack_eltBits α).symm

inductive Letter
  | x (i : Fin 4)
  | n (i : Fin 4)

namespace Letter

@[expose] def bits : Letter → ℕ
  | x i => pack (xCols i)
  | n i => pack (nCols i)

variable (K) in
@[expose] noncomputable def elt
    : Letter → adjointGroup ReeTag.F4.tag K
  | x i => xElement (idx i) 1
  | n i => weylElement ReeTag.F4.tag K (idx i)

@[expose] def flip : Letter → Letter
  | x i => x (3 - i)
  | n i => n (3 - i)

theorem hasBits
    [CharP K 2] : ∀ l : Letter, HasBits K (l.elt K) l.bits
  | x i => by
    have h := toEnd_pack_eltBits (K := K) (simpleRoot ReeTag.F4.tag (idx i))
    rw [rootPos_simpleRoot, show ((idx i : Fin ReeTag.F4.tag.rank) : ℕ) = i from rfl] at h
    rw [HasBits, bits, ← eltBits_eq_xCols, h, (rootOperatorFamily ReeTag.F4.tag).elt_simple]
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
    have h : (weylElement ReeTag.F4.tag K (idx i))⁻¹ = weylElement ReeTag.F4.tag K (idx i) :=
      Subtype.ext (by
        change (weylElt ReeTag.F4.tag K (idx i) 1)⁻¹ = weylElt ReeTag.F4.tag K (idx i) 1
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
    (w : List Letter) : adjointGroup ReeTag.F4.tag K :=
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
    evalG K w = evalG K w' ↔ evalB w % 2 ^ 2704 = evalB w' % 2 ^ 2704 :=
  (hasBits_evalG w).eq_iff (hasBits_evalG w')

theorem eltElement_eq_evalG_iff
    [CharP K 2] (α : Root ReeTag.F4.tag) (w : List Letter) :
    (rootOperatorFamily ReeTag.F4.tag).eltElement α 1 = evalG K w ↔
      pack (eltBits (rootPos α)) % 2 ^ 2704 = evalB w % 2 ^ 2704 :=
  (hasBits_eltElement α).eq_iff (hasBits_evalG w)

end CFSG.LieType.Simplicity.TitsBits
