module

public import CFSG.Certificates.Kernel.Spor.Mat3Sound
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeCodes
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.G2Three

open CFSG.KS.Mat3 CFSG.KC.Ord CFSG.RankThree.PartTwo.Census.Carrier.G2Three

@[expose] def bitsOf (f : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | e :: r => 2 * bitsOf f r + (if f e then 1 else 0)

theorem testBit_bitsOf (f : ℕ → Bool) :
    ∀ (l : List ℕ) (t : ℕ), (bitsOf f l).testBit t = (decide (t < l.length) && f (l.getD t 0))
  | [], t => by simp [bitsOf]
  | e :: r, 0 => by
    unfold bitsOf
    rw [Nat.testBit_zero]
    cases h : f e <;> simp [h, Nat.mul_add_mod]
  | e :: r, t + 1 => by
    unfold bitsOf
    have e2 : (2 * bitsOf f r + (if f e = true then 1 else 0)) / 2 = bitsOf f r := by
      split <;> omega
    rw [Nat.testBit_succ, e2, testBit_bitsOf f r t]
    simp

theorem bitsOf_lt (f : ℕ → Bool) : ∀ l : List ℕ, bitsOf f l < 2 ^ l.length
  | [] => by simp [bitsOf]
  | e :: r => by
    unfold bitsOf
    have := bitsOf_lt f r
    rw [List.length_cons, Nat.pow_succ]
    split <;> omega

@[expose] def pk (m : List ℕ) : ℕ := 2 ^ 196 * bitsOf (· == 2) m + bitsOf (· == 1) m

theorem canon14_iff {m : List ℕ} : canon14 m = true ↔ m.length = 196 ∧ ∀ e ∈ m, e < 3 := by
  simp [canon14]

theorem testBit_pk_lo {m : List ℕ} (hm : m.length = 196) {t : ℕ} (ht : t < 196) :
    (pk m).testBit t = (m.getD t 0 == 1) := by
  have hlt : bitsOf (· == 1) m < 2 ^ 196 := hm ▸ bitsOf_lt _ m
  unfold pk
  rw [Nat.testBit_two_pow_mul_add _ hlt, if_pos ht, testBit_bitsOf, hm]
  simp [ht]

theorem testBit_pk_hi {m : List ℕ} (hm : m.length = 196) {t : ℕ} (ht : t < 196) :
    (pk m).testBit (196 + t) = (m.getD t 0 == 2) := by
  have hlt : bitsOf (· == 1) m < 2 ^ 196 := hm ▸ bitsOf_lt _ m
  unfold pk
  rw [Nat.testBit_two_pow_mul_add _ hlt, if_neg (by omega), Nat.add_sub_cancel_left,
    testBit_bitsOf, hm]
  simp [ht]

theorem pk_lt {m : List ℕ} (hm : m.length = 196) : pk m < 2 ^ (196 + 196) := by
  have h1 : bitsOf (· == 1) m < 2 ^ 196 := hm ▸ bitsOf_lt _ m
  have h2 : bitsOf (· == 2) m < 2 ^ 196 := hm ▸ bitsOf_lt _ m
  unfold pk
  rw [Nat.pow_add]
  have : 2 ^ 196 * bitsOf (· == 2) m + 2 ^ 196 ≤ 2 ^ 196 * 2 ^ 196 := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ h2
  omega

set_option exponentiation.threshold 512 in
theorem pk_canon {m : List ℕ} (hm : canon14 m = true) : Canon3 196 (pk m) := by
  have hl := (canon14_iff.1 hm).1
  refine ⟨pk_lt hl, fun t ht => ?_⟩
  by_cases h : t < 196
  · rw [testBit_pk_lo hl h] at ht
    rw [testBit_pk_hi hl h]
    rw [beq_iff_eq] at ht
    rw [ht]
    rfl
  · apply Nat.testBit_lt_two_pow
    exact lt_of_lt_of_le (pk_lt hl) (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem getD_lt3 {m : List ℕ} (hm : canon14 m = true) (t : ℕ) : m.getD t 0 < 3 := by
  obtain ⟨-, h⟩ := canon14_iff.1 hm
  rw [List.getD_eq_getElem?_getD]
  cases hg : m[t]? with
  | none => simp
  | some e => exact h e (List.mem_of_getElem? hg)

theorem mat3_pk {m : List ℕ} (hm : canon14 m = true) (i j : Fin 14) :
    mat3 14 196 (pk m) i j = dec14 m i j := by
  have hl := (canon14_iff.1 hm).1
  have hi := i.isLt
  have hj := j.isLt
  have hij : 14 * i.val + j.val < 196 := by omega
  unfold mat3 dec14
  rw [testBit_pk_lo hl hij, testBit_pk_hi hl hij]
  simp only [Matrix.of_apply]
  have h3 := getD_lt3 hm (14 * i.val + j.val)
  generalize m.getD (14 * i.val + j.val) 0 = e at h3 ⊢
  interval_cases e <;> decide

theorem mat3_pk_eq {m : List ℕ} (hm : canon14 m = true) :
    mat3 14 196 (pk m) = dec14 m := by
  funext i j
  exact mat3_pk hm i j

theorem pk_inj {m n : List ℕ} (hm : canon14 m = true) (hn : canon14 n = true) (h : pk m = pk n) :
    m = n :=
  dec14_injective hm hn (by rw [← mat3_pk_eq hm, ← mat3_pk_eq hn, h])

theorem pk_mul14 {f LO RM CI ONE UP : ℕ} (hc : consts3OK 14 f 196 LO RM CI ONE UP = true)
    {m n : List ℕ} (hm : canon14 m = true) (hn : canon14 n = true) :
    pk (mul14 m n) = mul3s 14 196 LO CI RM (pk m) (pk n) := by
  obtain ⟨h1, h2⟩ := mul3s_sound hc (pk_canon hm) (pk_canon hn)
  exact mat3_inj rfl (pk_canon (canon14_mul14 m n)) h1
    (by rw [h2, mat3_pk_eq hm, mat3_pk_eq hn, mat3_pk_eq (canon14_mul14 m n), dec14_mul14])

end CFSG.KC.G2Three

end
