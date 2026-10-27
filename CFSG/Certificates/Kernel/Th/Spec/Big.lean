module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] def pkMat (N : ℕ) : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  Matrix.of fun i j => if N.testBit (256 * i.val + j.val) then 1 else 0

@[expose] def InLayout (N : ℕ) : Prop :=
  ∀ b, N.testBit b = true → b % 256 < 248 ∧ b / 256 < 248

theorem pkMat_apply (N : ℕ) (i j : Fin 248) :
    pkMat N i j = if N.testBit (256 * i.val + j.val) then 1 else 0 := rfl

theorem pkMat_inj {A B : ℕ} (hA : InLayout A) (hB : InLayout B) (h : pkMat A = pkMat B) :
    A = B := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b % 256 < 248 ∧ b / 256 < 248
  · have := congrFun (congrFun h ⟨b / 256, hb.2⟩) ⟨b % 256, hb.1⟩
    rw [pkMat_apply, pkMat_apply] at this
    have e : 256 * (b / 256) + b % 256 = b := by omega
    simp only [e] at this
    cases ha : A.testBit b <;> cases hb' : B.testBit b <;> simp_all <;>
      exact absurd this (by decide)
  · rw [Bool.eq_false_iff.2 (fun hh => hb (hA b hh)), Bool.eq_false_iff.2 (fun hh => hb (hB b hh))]

private theorem rep_succ_eq (x s n : ℕ) : rep x s (n + 1) = rep x s n ||| x <<< (s * n) := rfl

private theorem testBit_rep_one (s : ℕ) :
    ∀ m k, (rep 1 s m).testBit k = true ↔ ∃ i < m, k = s * i
  | 0, k => by simp [rep]
  | m + 1, k => by
    rw [rep_succ_eq, Nat.testBit_or, Bool.or_eq_true, testBit_rep_one s m k, Nat.one_shiftLeft,
      Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, hk⟩ | h)
      · exact ⟨i, by omega, hk⟩
      · exact ⟨m, by omega, h.symm⟩
    · rintro ⟨i, hi, hk⟩
      by_cases him : i = m
      · right
        subst him
        exact hk.symm
      · left
        exact ⟨i, by omega, hk⟩

private theorem testBit_c (p : ℕ) :
    (rep 1 256 248).testBit p = decide (p % 256 = 0 ∧ p / 256 < 248) := by
  rw [Bool.eq_iff_iff, testBit_rep_one, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨p / 256, h.2, by omega⟩

private theorem rep_lt (s : ℕ) (hs : 0 < s) (m : ℕ) : rep 1 s m < 2 ^ (s * m) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨i, hi, rfl⟩ := (testBit_rep_one s m j).1 h
  have : s * i < s * m := Nat.mul_lt_mul_of_pos_left hi hs
  omega

private noncomputable def colmT (s n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun c acc => Bool.rec (motive := fun _ => ℕ) (Nat.lor acc (Nat.shiftLeft (nat_lit 1) c)) acc
      (Nat.beq (Nat.land c s) (nat_lit 0))) n

private noncomputable def rowmT (s row n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun r acc => Bool.rec (motive := fun _ => ℕ) acc
      (Nat.lor acc (Nat.shiftLeft row (Nat.mul (nat_lit 256) r)))
      (Nat.beq (Nat.land r s) (nat_lit 0))) n

private theorem tmask_eq_rowm (k : ℕ) : tmask k = rowmT (Nat.shiftLeft (nat_lit 1) k)
    (colmT (Nat.shiftLeft (nat_lit 1) k) (nat_lit 256)) (nat_lit 256) := by
  unfold tmask rowmT colmT
  rfl

private theorem colmT_succ (s n : ℕ) : colmT s (n + 1) =
    if Nat.beq (n &&& s) 0 = true then colmT s n else colmT s n ||| 1 <<< n := by
  change Bool.rec (motive := fun _ => ℕ) (colmT s n ||| 1 <<< n) (colmT s n)
    (Nat.beq (n &&& s) 0) = _
  cases Nat.beq (n &&& s) 0 <;> rfl

private theorem rowmT_succ (s row n : ℕ) : rowmT s row (n + 1) =
    if Nat.beq (n &&& s) 0 = true then rowmT s row n ||| row <<< (256 * n) else rowmT s row n := by
  change Bool.rec (motive := fun _ => ℕ) (rowmT s row n) (rowmT s row n ||| row <<< (256 * n))
    (Nat.beq (n &&& s) 0) = _
  cases Nat.beq (n &&& s) 0 <;> rfl

private theorem colmT_bits (s j : ℕ) : ∀ n,
    (colmT s n).testBit j = (decide (j < n) && !Nat.beq (j &&& s) 0)
  | 0 => by simp [colmT]
  | n + 1 => by
    rw [colmT_succ]
    by_cases e : j = n
    · subst e
      cases h : Nat.beq (j &&& s) 0
      · simp [Nat.testBit_or, colmT_bits s j j, h, Nat.one_shiftLeft]
      · simp [colmT_bits s j j, h]
    · have e' : j < n + 1 ↔ j < n := by omega
      have e2 : ¬ n = j := fun h => e h.symm
      cases h : Nat.beq (n &&& s) 0 <;>
        simp [colmT_bits s j n, e', Nat.testBit_or, e2, Nat.one_shiftLeft]

theorem testBit_shl_row {row : ℕ} (h : row < 2 ^ 256) (n p : ℕ) :
    (row <<< (256 * n)).testBit p = (decide (p / 256 = n) && row.testBit (p % 256)) := by
  rw [Nat.testBit_shiftLeft]
  by_cases e : p / 256 = n
  · have e1 : p - 256 * n = p % 256 := by omega
    have e2 : 256 * n ≤ p := by omega
    simp [e, e1, e2]
  · by_cases e2 : 256 * n ≤ p
    · have e3 : 256 ≤ p - 256 * n := by omega
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) e3))]
      simp [e]
    · simp [e, e2]

private theorem rowmT_bits (s : ℕ) {row : ℕ} (hrow : row < 2 ^ 256) (p : ℕ) : ∀ n,
    (rowmT s row n).testBit p =
      (decide (p / 256 < n) && Nat.beq (p / 256 &&& s) 0 && row.testBit (p % 256))
  | 0 => by simp [rowmT]
  | n + 1 => by
    rw [rowmT_succ]
    by_cases e : p / 256 = n
    · cases h : Nat.beq (n &&& s) 0
      · simp [rowmT_bits s hrow p n, e, h]
      · simp [Nat.testBit_or, rowmT_bits s hrow p n, testBit_shl_row hrow, e, h]
    · have e' : p / 256 < n + 1 ↔ p / 256 < n := by omega
      cases h : Nat.beq (n &&& s) 0 <;>
        simp [Nat.testBit_or, rowmT_bits s hrow p n, testBit_shl_row hrow, e, e']

private theorem beq_and_two_pow (j k : ℕ) :
    Nat.beq (j &&& Nat.shiftLeft (nat_lit 1) k) 0 = !j.testBit k := by
  change Nat.beq (j &&& 1 <<< k) 0 = _
  cases h : j.testBit k
  · have e : j &&& 1 <<< k = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases e : k = i
      · subst e
        simp [h]
      · simp [e]
    rw [e]
    rfl
  · have e : (j &&& 1 <<< k).testBit k = true := by
      rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_self, h]
      rfl
    cases hb : Nat.beq (j &&& 1 <<< k) 0
    · rfl
    · rw [Nat.eq_of_beq_eq_true hb, Nat.zero_testBit] at e
      exact absurd e Bool.false_ne_true

private theorem colmT_lt (s : ℕ) : colmT s (nat_lit 256) < 2 ^ 256 :=
  Nat.lt_pow_two_of_testBit _ (fun j hj => by
    rw [colmT_bits]
    have : ¬ j < 256 := by omega
    simp [this])

private theorem tmask_dec (k p : ℕ) : (tmask k).testBit p =
    decide (p / 256 < 256 ∧ p / 256 / 2 ^ k % 2 = 0 ∧ p % 256 / 2 ^ k % 2 = 1) := by
  rw [tmask_eq_rowm, rowmT_bits _ (colmT_lt _), colmT_bits, beq_and_two_pow, beq_and_two_pow,
    Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hc : p % 256 < 256 := Nat.mod_lt _ (by omega)
  rcases Nat.mod_two_eq_zero_or_one (p / 256 / 2 ^ k) with h | h <;> simp [h, hc]

private noncomputable def piK (s p : ℕ) : ℕ :=
  if p / 256 < 256 ∧ p / 256 / s % 2 = 0 ∧ p % 256 / s % 2 = 1 then p + 255 * s
  else if p / 256 < 256 ∧ p / 256 / s % 2 = 1 ∧ p % 256 / s % 2 = 0 then p - 255 * s else p

private theorem lvl_bit {k s : ℕ} (hk : k < 8) (hs : s = 2 ^ k) (x p : ℕ) :
    (trLvl s (tmask k) x).testBit p = x.testBit (piK s p) := by
  change (x ^^^ (((x ^^^ x >>> (255 * s)) &&& tmask k) |||
    ((x ^^^ x >>> (255 * s)) &&& tmask k) <<< (255 * s))).testBit p = _
  have hs8 : s = 1 ∨ s = 2 ∨ s = 4 ∨ s = 8 ∨ s = 16 ∨ s = 32 ∨ s = 64 ∨ s = 128 := by
    have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hs]
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, tmask_dec, ← hs]
  unfold piK
  by_cases h1 : p / 256 < 256 ∧ p / 256 / s % 2 = 0 ∧ p % 256 / s % 2 = 1
  · have h3 : 255 * s ≤ p → ¬ ((p - 255 * s) / 256 < 256 ∧ (p - 255 * s) / 256 / s % 2 = 0 ∧
        (p - 255 * s) % 256 / s % 2 = 1) := by
      rcases hs8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [ite_eq_left h1, Nat.add_comm (255 * s) p]
    by_cases h4 : 255 * s ≤ p
    · simp [h1, h3 h4, h4]
    · simp [h1, h4]
  · rw [ite_eq_right h1]
    by_cases h2 : p / 256 < 256 ∧ p / 256 / s % 2 = 1 ∧ p % 256 / s % 2 = 0
    · have h4 : 255 * s ≤ p ∧ ((p - 255 * s) / 256 < 256 ∧ (p - 255 * s) / 256 / s % 2 = 0 ∧
          (p - 255 * s) % 256 / s % 2 = 1) := by
        rcases hs8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [ite_eq_left h2, Nat.add_sub_cancel' h4.1]
      simp only [h1, h4, decide_false, decide_true, Bool.and_false, Bool.false_or, Bool.true_and]
      cases x.testBit p <;> cases x.testBit (p - 255 * s) <;> rfl
    · have h3 : 255 * s ≤ p → ¬ ((p - 255 * s) / 256 < 256 ∧ (p - 255 * s) / 256 / s % 2 = 0 ∧
          (p - 255 * s) % 256 / s % 2 = 1) := by
        rcases hs8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [ite_eq_right h2]
      by_cases h4 : 255 * s ≤ p
      · simp [h1, h3 h4, h4]
      · simp [h1, h4]

private def posB (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) : ℕ :=
  256 * (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7) +
    (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5 + 64 * b6 + 128 * b7)

section Swap

variable {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ} (h0 : a0 ≤ 1) (h1 : a1 ≤ 1)
  (h2 : a2 ≤ 1) (h3 : a3 ≤ 1) (h4 : a4 ≤ 1) (h5 : a5 ≤ 1) (h6 : a6 ≤ 1) (h7 : a7 ≤ 1)
  (g0 : b0 ≤ 1) (g1 : b1 ≤ 1) (g2 : b2 ≤ 1) (g3 : b3 ≤ 1) (g4 : b4 ≤ 1) (g5 : b5 ≤ 1)
  (g6 : b6 ≤ 1) (g7 : b7 ≤ 1)
include h0 h1 h2 h3 h4 h5 h6 h7 g0 g1 g2 g3 g4 g5 g6 g7

private theorem piK0 : piK 1 (posB a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7) =
    posB b0 a1 a2 a3 a4 a5 a6 a7 a0 b1 b2 b3 b4 b5 b6 b7 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK1 : piK 2 (posB a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7) =
    posB a0 b1 a2 a3 a4 a5 a6 a7 b0 a1 b2 b3 b4 b5 b6 b7 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK2 : piK 4 (posB a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7) =
    posB a0 a1 b2 a3 a4 a5 a6 a7 b0 b1 a2 b3 b4 b5 b6 b7 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK3 : piK 8 (posB a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7) =
    posB a0 a1 a2 b3 a4 a5 a6 a7 b0 b1 b2 a3 b4 b5 b6 b7 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK4 : piK 16 (posB a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7) =
    posB a0 a1 a2 a3 b4 a5 a6 a7 b0 b1 b2 b3 a4 b5 b6 b7 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK5 : piK 32 (posB a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7) =
    posB a0 a1 a2 a3 a4 b5 a6 a7 b0 b1 b2 b3 b4 a5 b6 b7 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK6 : piK 64 (posB a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7) =
    posB a0 a1 a2 a3 a4 a5 b6 a7 b0 b1 b2 b3 b4 b5 a6 b7 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK7 : piK 128 (posB a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7) =
    posB a0 a1 a2 a3 a4 a5 a6 b7 b0 b1 b2 b3 b4 b5 b6 a7 := by
  unfold piK posB
  split_ifs <;> omega

end Swap

private theorem bits8 {r : ℕ} (hr : r < 256) : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : ℕ, a0 ≤ 1 ∧ a1 ≤ 1 ∧
    a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1 ∧ a7 ≤ 1 ∧
    r = a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 + 128 * a7 :=
  ⟨r % 2, r / 2 % 2, r / 4 % 2, r / 8 % 2, r / 16 % 2, r / 32 % 2, r / 64 % 2, r / 128 % 2,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem piK_big {s p : ℕ} (h : 256 ≤ p / 256) : piK s p = p := by
  unfold piK
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem piK_all (p : ℕ) :
    piK 128 (piK 64 (piK 32 (piK 16 (piK 8 (piK 4 (piK 2 (piK 1 p))))))) =
      if p / 256 < 256 then 256 * (p % 256) + p / 256 else p := by
  by_cases hp : p / 256 < 256
  · rw [ite_eq_left hp]
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, h0, h1, h2, h3, h4, h5, h6, h7, ha⟩ := bits8 hp
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, g0, g1, g2, g3, g4, g5, g6, g7, hb⟩ :=
      bits8 (Nat.mod_lt p (by omega : 256 > 0))
    have e : p = posB a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 := by
      unfold posB
      omega
    rw [ha, hb, e, piK0 h0 h1 h2 h3 h4 h5 h6 h7 g0 g1 g2 g3 g4 g5 g6 g7,
      piK1 g0 h1 h2 h3 h4 h5 h6 h7 h0 g1 g2 g3 g4 g5 g6 g7,
      piK2 g0 g1 h2 h3 h4 h5 h6 h7 h0 h1 g2 g3 g4 g5 g6 g7,
      piK3 g0 g1 g2 h3 h4 h5 h6 h7 h0 h1 h2 g3 g4 g5 g6 g7,
      piK4 g0 g1 g2 g3 h4 h5 h6 h7 h0 h1 h2 h3 g4 g5 g6 g7,
      piK5 g0 g1 g2 g3 g4 h5 h6 h7 h0 h1 h2 h3 h4 g5 g6 g7,
      piK6 g0 g1 g2 g3 g4 g5 h6 h7 h0 h1 h2 h3 h4 h5 g6 g7,
      piK7 g0 g1 g2 g3 g4 g5 g6 h7 h0 h1 h2 h3 h4 h5 h6 g7]
    unfold posB
    omega
  · rw [ite_eq_right hp]
    have hb : 256 ≤ p / 256 := by omega
    rw [piK_big hb, piK_big hb, piK_big hb, piK_big hb, piK_big hb, piK_big hb, piK_big hb,
      piK_big hb]

theorem trB_bit (x p : ℕ) :
    (trB (tmask 0) (tmask 1) (tmask 2) (tmask 3) (tmask 4) (tmask 5) (tmask 6) (tmask 7) x).testBit
      p = x.testBit (if p / 256 < 256 then 256 * (p % 256) + p / 256 else p) := by
  change (trLvl 1 (tmask 0) (trLvl 2 (tmask 1) (trLvl 4 (tmask 2) (trLvl 8 (tmask 3)
    (trLvl 16 (tmask 4) (trLvl 32 (tmask 5) (trLvl 64 (tmask 6)
      (trLvl 128 (tmask 7) x)))))))).testBit p = _
  rw [lvl_bit (k := 0) (s := 1) (by omega) rfl, lvl_bit (k := 1) (s := 2) (by omega) rfl,
    lvl_bit (k := 2) (s := 4) (by omega) rfl, lvl_bit (k := 3) (s := 8) (by omega) rfl,
    lvl_bit (k := 4) (s := 16) (by omega) rfl, lvl_bit (k := 5) (s := 32) (by omega) rfl,
    lvl_bit (k := 6) (s := 64) (by omega) rfl, lvl_bit (k := 7) (s := 128) (by omega) rfl,
    piK_all]

private theorem add_eq_or_of_land_eq_zero (a b : ℕ) (h : a &&& b = 0) : a + b = a ||| b := by
  by_cases ha : a = 0
  · subst ha
    simp
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    have h' : a / 2 &&& b / 2 = 0 := by rw [← Nat.and_div_two, h]
    have ih := add_eq_or_of_land_eq_zero (a / 2) (b / 2) h'
    have h1 : (a ||| b) / 2 = a / 2 ||| b / 2 := Nat.or_div_two
    have h2 := @Nat.or_mod_two_eq_one a b
    have h3 : ¬ ((a &&& b) % 2 = 1) := by rw [h]; decide
    rw [Nat.and_mod_two_eq_one] at h3
    omega
termination_by a

private theorem testBit_mul_pred {u : ℕ} (hu : ∀ q, u.testBit q = true → q % 256 = 0) :
    ∀ n, n ≤ 256 → ∀ p, (u * (2 ^ n - 1)).testBit p =
      (decide (p % 256 < n) && u.testBit (256 * (p / 256)))
  | 0, _, p => by simp
  | n + 1, hn, p => by
    have ih := testBit_mul_pred hu n (by omega)
    have h2 : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + 2 ^ n := by
      have := Nat.one_le_two_pow (n := n)
      rw [Nat.pow_succ]
      omega
    have hb : ∀ q, (u * 2 ^ n).testBit q = (decide (n ≤ q) && u.testBit (q - n)) := fun q => by
      rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    have hdis : (u * (2 ^ n - 1)) &&& (u * 2 ^ n) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro q
      rw [Nat.testBit_and, ih, hb, Nat.zero_testBit, Bool.eq_false_iff]
      intro hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      obtain ⟨⟨h1, -⟩, h3, h4⟩ := hq
      have := hu _ h4
      omega
    rw [h2, Nat.mul_add, add_eq_or_of_land_eq_zero _ _ hdis, Nat.testBit_or, ih, hb,
      Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by omega, h2⟩
      · have h0 := hu _ h2
        have e : p - n = 256 * (p / 256) := by omega
        rw [e] at h2
        exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases h3 : p % 256 < n
      · exact Or.inl ⟨h3, h2⟩
      · right
        have e : p - n = 256 * (p / 256) := by omega
        rw [e]
        exact ⟨by omega, h2⟩

private theorem testBit_mul_rep {v : ℕ} (hv : v < 2 ^ 256) :
    ∀ n p, (v * rep 1 256 n).testBit p = (decide (p / 256 < n) && v.testBit (p % 256))
  | 0, p => by simp [rep]
  | n + 1, p => by
    have ih := testBit_mul_rep hv n
    have hlt : v * rep 1 256 n < 2 ^ (256 * n) := by
      apply Nat.lt_pow_two_of_testBit
      intro j hj
      rw [ih j]
      have : ¬ j / 256 < n := by omega
      simp [this]
    have hrep : rep 1 256 (n + 1) = rep 1 256 n + 2 ^ (256 * n) := by
      rw [rep_succ_eq, Nat.one_shiftLeft]
      exact Nat.or_two_pow_eq_add_of_lt (rep_lt 256 (by omega) n)
    have e : v * rep 1 256 (n + 1) = (v <<< (256 * n)) ||| (v * rep 1 256 n) := by
      rw [← Nat.shiftLeft_add_eq_or_of_lt hlt, hrep, Nat.mul_add, Nat.shiftLeft_eq, Nat.add_comm]
    rw [e, Nat.testBit_or, testBit_shl_row hv n p, ih p]
    by_cases h1 : p / 256 < n
    · simp [h1, show ¬ p / 256 = n by omega, show p / 256 < n + 1 by omega]
    · by_cases h2 : p / 256 = n
      · simp [h1, h2]
      · simp [h1, h2, show ¬ p / 256 < n + 1 by omega]

private def xsB (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => xsB f n ^^ f n

private def stepP (c rm A B k : ℕ) : ℕ :=
  ((A >>> k) &&& c) * rm &&& ((B >>> (k * 256)) &&& rm) * c

private noncomputable def mulBn (c rm A B n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => mstep c rm A B acc k (k * 256)) n

private theorem mulB_eq_mulBn (c rm A B : ℕ) : mulB c rm A B = mulBn c rm A B 248 := rfl

private theorem mulBn_succ (c rm A B n : ℕ) :
    mulBn c rm A B (n + 1) = mulBn c rm A B n ^^^ stepP c rm A B n := rfl

private theorem testBit_stepP {A B k : ℕ} (hk : k < 248) (p : ℕ) :
    (stepP (rep 1 256 248) (2 ^ 248 - 1) A B k).testBit p =
      (decide (p % 256 < 248 ∧ p / 256 < 248) &&
        (A.testBit (256 * (p / 256) + k) && B.testBit (256 * k + p % 256))) := by
  unfold stepP
  rw [Nat.testBit_and]
  have hu : ∀ q, ((A >>> k) &&& rep 1 256 248).testBit q = true → q % 256 = 0 := by
    intro q hq
    rw [Nat.testBit_and, testBit_c, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2.1
  have hv : ((B >>> (k * 256)) &&& (2 ^ 248 - 1)) < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by omega)))
      (Nat.pow_le_pow_right (by omega) (by omega))
  rw [testBit_mul_pred hu 248 (by omega), testBit_mul_rep hv 248, Nat.testBit_and,
    Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight, testBit_c,
    Nat.testBit_two_pow_sub_one]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have e1 : 256 * (p / 256) % 256 = 0 := by omega
  have e2 : 256 * (p / 256) / 256 = p / 256 := by omega
  rw [e1, e2, Nat.add_comm k, Nat.mul_comm k]
  simp only [true_and]
  tauto

private theorem testBit_mulBn {A B : ℕ} (p : ℕ) : ∀ n, n ≤ 248 →
    (mulBn (rep 1 256 248) (2 ^ 248 - 1) A B n).testBit p =
      (decide (p % 256 < 248 ∧ p / 256 < 248) &&
        xsB (fun k => A.testBit (256 * (p / 256) + k) && B.testBit (256 * k + p % 256)) n)
  | 0, _ => by simp [mulBn, xsB]
  | n + 1, hn => by
    rw [mulBn_succ, Nat.testBit_xor, testBit_mulBn p n (by omega), testBit_stepP (by omega) p,
      xsB]
    cases decide (p % 256 < 248 ∧ p / 256 < 248) <;> simp

private theorem zmod2_xsB (f : ℕ → Bool) : ∀ n,
    (if xsB f n then (1 : ZMod 2) else 0) = ∑ k ∈ Finset.range n, (if f k then 1 else 0)
  | 0 => by simp [xsB]
  | n + 1 => by
    rw [xsB, Finset.sum_range_succ, ← zmod2_xsB f n]
    cases xsB f n <;> cases f n <;> decide

private theorem pkMat_mulB_rep (A B : ℕ) :
    pkMat (mulB (rep 1 256 248) (2 ^ 248 - 1) A B) = pkMat A * pkMat B := by
  ext i j
  rw [Matrix.mul_apply, pkMat_apply, mulB_eq_mulBn, testBit_mulBn _ 248 le_rfl]
  have e1 : (256 * i.val + j.val) % 256 = j.val := by omega
  have e2 : (256 * i.val + j.val) / 256 = i.val := by omega
  have hi := i.isLt
  have hj := j.isLt
  rw [e1, e2, show decide (j.val < 248 ∧ i.val < 248) = true by simp [hi, hj], Bool.true_and,
    zmod2_xsB, ← Fin.sum_univ_eq_sum_range (fun k => if A.testBit (256 * i.val + k) &&
      B.testBit (256 * k + j.val) then (1 : ZMod 2) else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pkMat_apply, pkMat_apply]
  cases A.testBit (256 * i.val + k.val) <;> cases B.testBit (256 * k.val + j.val) <;> simp

private theorem inLayout_mulB_rep (A B : ℕ) :
    InLayout (mulB (rep 1 256 248) (2 ^ 248 - 1) A B) := by
  intro b hb
  rw [mulB_eq_mulBn, testBit_mulBn _ 248 le_rfl, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hb.1

private theorem pkMat_trB_rep (A : ℕ) :
    pkMat (trB (tmask 0) (tmask 1) (tmask 2) (tmask 3) (tmask 4) (tmask 5) (tmask 6) (tmask 7) A) =
      (pkMat A).transpose := by
  ext i j
  rw [Matrix.transpose_apply, pkMat_apply, pkMat_apply, trB_bit]
  have hi := i.isLt
  have hj := j.isLt
  have e1 : (256 * i.val + j.val) / 256 < 256 := by omega
  have e2 : (256 * i.val + j.val) % 256 = j.val := by omega
  have e3 : (256 * i.val + j.val) / 256 = i.val := by omega
  rw [if_pos e1, e2, e3]

private theorem inLayout_trB_rep {A : ℕ} (hA : InLayout A) :
    InLayout (trB (tmask 0) (tmask 1) (tmask 2) (tmask 3) (tmask 4) (tmask 5) (tmask 6) (tmask 7)
      A) := by
  intro b hb
  rw [trB_bit] at hb
  by_cases h : b / 256 < 256
  · rw [if_pos h] at hb
    have := hA _ hb
    have hr : b % 256 < 256 := Nat.mod_lt _ (by omega)
    generalize b % 256 = r at *
    generalize b / 256 = q at *
    omega
  · rw [if_neg h] at hb
    have := hA _ hb
    omega

private theorem pkMat_dg : pkMat (rep 1 257 248) = 1 := by
  ext i j
  rw [pkMat_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i = j
  · subst h
    have : (rep 1 257 248).testBit (256 * i.val + i.val) = true :=
      (testBit_rep_one 257 248 _).2 ⟨i.val, hi, by omega⟩
    simp [this]
  · have : (rep 1 257 248).testBit (256 * i.val + j.val) = false := by
      rw [Bool.eq_false_iff]
      intro hb
      obtain ⟨r, hr, e⟩ := (testBit_rep_one 257 248 _).1 hb
      exact h (Fin.ext (by omega))
    simp [h, this]

private theorem inLayout_dg : InLayout (rep 1 257 248) := by
  intro b hb
  obtain ⟨r, hr, e⟩ := (testBit_rep_one 257 248 _).1 hb
  have h2 := (Nat.div_mod_unique (a := b) (b := 256) (c := r) (d := r) (by omega)).2
    ⟨by omega, by omega⟩
  omega

private noncomputable def powBn (c rm ONE M e nb n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) ONE
    (fun i acc => (fun sq => Bool.rec (motive := fun _ => ℕ) sq (mulB c rm sq M)
        (Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (Nat.sub nb (nat_lit 1)) i)) (nat_lit 1))
          (nat_lit 1)))
      (mulB c rm acc acc)) n

private theorem powB_eq_powBn (c rm ONE M e nb : ℕ) :
    powB c rm ONE M e nb = powBn c rm ONE M e nb nb := rfl

private theorem powBn_succ_raw (c rm ONE M e nb n : ℕ) :
    powBn c rm ONE M e nb (n + 1) =
      Bool.rec (motive := fun _ => ℕ)
        (mulB c rm (powBn c rm ONE M e nb n) (powBn c rm ONE M e nb n))
        (mulB c rm (mulB c rm (powBn c rm ONE M e nb n) (powBn c rm ONE M e nb n)) M)
        (Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (Nat.sub nb 1) n)) 1) 1) := rfl

private theorem powBn_succ (c rm ONE M e nb n : ℕ) :
    powBn c rm ONE M e nb (n + 1) =
      if (e >>> (nb - 1 - n)) % 2 = 1 then
        mulB c rm (mulB c rm (powBn c rm ONE M e nb n) (powBn c rm ONE M e nb n)) M
      else mulB c rm (powBn c rm ONE M e nb n) (powBn c rm ONE M e nb n) := by
  have hb : Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (Nat.sub nb 1) n)) 1) 1 =
      decide ((e >>> (nb - 1 - n)) % 2 = 1) := by
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
    change (e >>> (nb - 1 - n)) &&& 1 = 1 ↔ _
    rw [Nat.and_one_is_mod]
  rw [powBn_succ_raw, hb]
  by_cases h : (e >>> (nb - 1 - n)) % 2 = 1
  · rw [if_pos h, decide_eq_true h]
  · rw [if_neg h, decide_eq_false h]

private theorem pkMat_powBn (ONE M e nb : ℕ) (h1 : pkMat ONE = 1) (he : e < 2 ^ nb) :
    ∀ n, n ≤ nb →
      pkMat (powBn (rep 1 256 248) (2 ^ 248 - 1) ONE M e nb n) = pkMat M ^ (e >>> (nb - n))
  | 0, _ => by
    rw [Nat.sub_zero, Nat.shiftRight_eq_zero e nb he, pow_zero]
    exact h1
  | n + 1, hn => by
    have ih := pkMat_powBn ONE M e nb h1 he n (by omega)
    have hm : nb - (n + 1) + 1 = nb - n := by omega
    have hy : e >>> (nb - n) = (e >>> (nb - (n + 1))) / 2 := by
      rw [← hm, Nat.shiftRight_succ]
    have hy2 : nb - 1 - n = nb - (n + 1) := by omega
    rw [powBn_succ, hy2]
    generalize e >>> (nb - (n + 1)) = y at hy ⊢
    split_ifs with hbit
    · rw [pkMat_mulB_rep, pkMat_mulB_rep, ih, hy, ← pow_add, ← pow_succ]
      congr 1
      omega
    · rw [pkMat_mulB_rep, ih, hy, ← pow_add]
      congr 1
      omega

private theorem inLayout_powBn (ONE M e nb : ℕ) (h1 : InLayout ONE) :
    ∀ n, InLayout (powBn (rep 1 256 248) (2 ^ 248 - 1) ONE M e nb n)
  | 0 => h1
  | n + 1 => by
    rw [powBn_succ]
    split_ifs
    · exact inLayout_mulB_rep _ _
    · exact inLayout_mulB_rep _ _

private theorem pkMat_powB_rep (ONE M e nb : ℕ) (h1 : pkMat ONE = 1) (he : e < 2 ^ nb) :
    pkMat (powB (rep 1 256 248) (2 ^ 248 - 1) ONE M e nb) = pkMat M ^ e := by
  rw [powB_eq_powBn, pkMat_powBn ONE M e nb h1 he nb le_rfl, Nat.sub_self, Nat.shiftRight_zero]

private theorem andB_split {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private noncomputable def upperN (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.sub (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 248)) (nat_lit 1))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.succ i)) (nat_lit 1))) (Nat.mul (nat_lit 256) i)))
    n

private theorem upper_eq_upperN : upper = upperN 248 := rfl

private theorem upperN_succ (n : ℕ) :
    upperN (n + 1) = upperN n ||| ((2 ^ 248 - 1 - (2 ^ (n + 1) - 1)) <<< (256 * n)) := by
  change upperN n ||| (((1 <<< 248) - 1 - ((1 <<< (n + 1)) - 1)) <<< (256 * n)) = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]

private theorem upperRow_bit {i : ℕ} (hi : i + 1 ≤ 248) (j : ℕ) :
    (2 ^ 248 - 1 - (2 ^ (i + 1) - 1)).testBit j = decide (i + 1 ≤ j ∧ j < 248) := by
  have hx : 2 ^ (i + 1) - 1 < 2 ^ 248 :=
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
      (Nat.pow_le_pow_right (by omega) hi)
  rw [Nat.sub_sub, Nat.add_comm 1, Nat.testBit_two_pow_sub_succ hx, Nat.testBit_two_pow_sub_one,
    Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

private theorem upperRow_lt (i : ℕ) : 2 ^ 248 - 1 - (2 ^ (i + 1) - 1) < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _)
    (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
      (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem testBit_upperN (p : ℕ) : ∀ n, n ≤ 248 →
    (upperN n).testBit p = decide (p / 256 < n ∧ p % 256 < 248 ∧ p / 256 < p % 256)
  | 0, _ => by simp [upperN]
  | n + 1, hn => by
    rw [upperN_succ, Nat.testBit_or, testBit_upperN p n (by omega),
      testBit_shl_row (upperRow_lt n) n p, upperRow_bit hn, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

private theorem chkUni_rep {M : ℕ} (hM : chkUni upper (rep 1 257 248) M = true) :
    (∀ i j : Fin 248, i < j → pkMat M i j = 0) ∧ ∀ i : Fin 248, pkMat M i i = 1 := by
  obtain ⟨h1, h2⟩ := andB_split hM
  have h1' : M &&& upper = 0 := Nat.eq_of_beq_eq_true h1
  have h2' : M &&& rep 1 257 248 = rep 1 257 248 := Nat.eq_of_beq_eq_true h2
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    have h3 := congrArg (fun x => x.testBit (256 * i.val + j.val)) h1'
    simp only [Nat.testBit_and, upper_eq_upperN, testBit_upperN _ 248 le_rfl,
      Nat.zero_testBit] at h3
    have e1 : (256 * i.val + j.val) / 256 = i.val := by omega
    have e2 : (256 * i.val + j.val) % 256 = j.val := by omega
    rw [e1, e2, show decide (i.val < 248 ∧ j.val < 248 ∧ i.val < j.val) = true by
      simp [hi, hj, hij']] at h3
    rw [pkMat_apply, Bool.and_true] at *
    rw [h3]
    rfl
  · have hi := i.isLt
    have h3 := congrArg (fun x => x.testBit (257 * i.val)) h2'
    simp only [Nat.testBit_and] at h3
    have h4 : (rep 1 257 248).testBit (257 * i.val) = true :=
      (testBit_rep_one 257 248 _).2 ⟨i.val, hi, rfl⟩
    rw [h4, Bool.and_true] at h3
    rw [pkMat_apply, show 256 * i.val + i.val = 257 * i.val by omega, h3]
    rfl

@[expose] def pkVec (v : ℕ) : Fin 248 → ZMod 2 := fun j => if v.testBit j.val then 1 else 0

theorem pkVec_apply (v : ℕ) (j : Fin 248) :
    pkVec v j = if v.testBit j.val then 1 else 0 := rfl

theorem pkVec_inj {v w : ℕ} (hv : v < 2 ^ 248) (hw : w < 2 ^ 248) (h : pkVec v = pkVec w) :
    v = w := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 248
  · have := congrFun h ⟨b, hb⟩
    rw [pkVec_apply, pkVec_apply] at this
    cases ha : v.testBit b <;> cases hb' : w.testBit b <;> simp_all <;>
      exact absurd this (by decide)
  · have h1 : 2 ^ 248 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv h1),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw h1)]

theorem pkVec_zero : pkVec 0 = 0 := by
  funext j
  simp [pkVec_apply]

theorem pkVec_xor (a b : ℕ) : pkVec (a ^^^ b) = pkVec a + pkVec b := by
  funext j
  rw [Pi.add_apply, pkVec_apply, pkVec_apply, pkVec_apply, Nat.testBit_xor]
  cases a.testBit j.val <;> cases b.testBit j.val <;> decide

theorem bitsN_eq (J o x : ℕ) : bitsN J o x = (J >>> o) % 2 ^ x := by
  unfold bitsN
  change (J >>> o) &&& (1 <<< x - 1) = _
  rw [Nat.one_shiftLeft]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private noncomputable def vecBn (rm v M n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight v k) 1)
      (Nat.land (Nat.shiftRight M (Nat.mul k 256)) rm))) n

private theorem vecB_eq_vecBn (rm v M : ℕ) : vecB rm v M = vecBn rm v M 248 := rfl

private theorem vecBn_succ (rm v M n : ℕ) : vecBn rm v M (n + 1) =
    vecBn rm v M n ^^^ (((v >>> n) &&& 1) * ((M >>> (n * 256)) &&& rm)) := rfl

private theorem testBit_vecTerm (v M n j : ℕ) :
    (((v >>> n) &&& 1) * ((M >>> (n * 256)) &&& (2 ^ 248 - 1))).testBit j =
      (v.testBit n && (M.testBit (256 * n + j) && decide (j < 248))) := by
  have h1 : (v >>> n) &&& 1 = if v.testBit n then 1 else 0 := by
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ n) with h | h <;> simp [h]
  rw [h1]
  cases hb : v.testBit n
  · simp
  · simp only [if_true, Nat.one_mul, Bool.true_and]
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Nat.mul_comm n 256,
      Nat.add_comm (256 * n)]

private theorem testBit_vecBn (v M j : ℕ) : ∀ n, n ≤ 248 →
    (vecBn (2 ^ 248 - 1) v M n).testBit j = (decide (j < 248) &&
      xsB (fun k => v.testBit k && M.testBit (256 * k + j)) n)
  | 0, _ => by simp [vecBn, xsB]
  | n + 1, hn => by
    rw [vecBn_succ, Nat.testBit_xor, testBit_vecBn v M j n (by omega), testBit_vecTerm, xsB]
    cases decide (j < 248) <;> cases v.testBit n <;> cases M.testBit (256 * n + j) <;>
      cases xsB (fun k => v.testBit k && M.testBit (256 * k + j)) n <;> rfl

private theorem vecB_lt_rep (v M : ℕ) : vecB (2 ^ 248 - 1) v M < 2 ^ 248 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [vecB_eq_vecBn, testBit_vecBn v M j 248 le_rfl]
  have : ¬ j < 248 := by omega
  simp [this]

private theorem pkVec_vecB_rep (v M : ℕ) :
    pkVec (vecB (2 ^ 248 - 1) v M) = Matrix.vecMul (pkVec v) (pkMat M) := by
  funext j
  rw [pkVec_apply, vecB_eq_vecBn, testBit_vecBn v M j 248 le_rfl]
  have hj := j.isLt
  rw [show decide (j.val < 248) = true by simp [hj], Bool.true_and, zmod2_xsB,
    ← Fin.sum_univ_eq_sum_range (fun k => if v.testBit k && M.testBit (256 * k + j.val) then
      (1 : ZMod 2) else 0)]
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pkVec_apply, pkMat_apply]
  cases v.testBit k.val <;> cases M.testBit (256 * k.val + j.val) <;> simp

@[expose] def wordLetter (A B Bi x : ℕ) : ℕ := if x = 0 then A else if x = 1 then B else Bi

private theorem beq_eq_decide (x k : ℕ) : Nat.beq x k = decide (x = k) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem wordAB_zero (c rm ONE A B Bi w : ℕ) : wordAB c rm ONE A B Bi w 0 = ONE := rfl

theorem wordAB_succ (c rm ONE A B Bi w n : ℕ) :
    wordAB c rm ONE A B Bi w (n + 1) =
      mulB c rm (wordAB c rm ONE A B Bi w n) (wordLetter A B Bi (bitsN w (2 * n) 2)) := by
  change mulB c rm (wordAB c rm ONE A B Bi w n)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) Bi B
      (Nat.beq (bitsN w (2 * n) 2) 1)) A (Nat.beq (bitsN w (2 * n) 2) 0)) = _
  generalize bitsN w (2 * n) 2 = x
  unfold wordLetter
  by_cases h0 : x = 0
  · subst h0
    rfl
  · by_cases h1 : x = 1
    · subst h1
      rfl
    · rw [if_neg h0, if_neg h1, beq_eq_decide, beq_eq_decide, decide_eq_false h0,
        decide_eq_false h1]

theorem consts_spec {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
    (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true) :
    c = rep 1 256 248 ∧ rm = 2 ^ 248 - 1 ∧ tm0 = tmask 0 ∧ tm1 = tmask 1 ∧ tm2 = tmask 2 ∧
      tm3 = tmask 3 ∧ tm4 = tmask 4 ∧ tm5 = tmask 5 ∧ tm6 = tmask 6 ∧ tm7 = tmask 7 ∧
      up = upper ∧ dg = rep 1 257 248 ∧ ONE = dg := by
  unfold constsOK at h
  obtain ⟨hc, h⟩ := andB_split h
  obtain ⟨hrm, h⟩ := andB_split h
  obtain ⟨h0, h⟩ := andB_split h
  obtain ⟨h1, h⟩ := andB_split h
  obtain ⟨h2, h⟩ := andB_split h
  obtain ⟨h3, h⟩ := andB_split h
  obtain ⟨h4, h⟩ := andB_split h
  obtain ⟨h5, h⟩ := andB_split h
  obtain ⟨h6, h⟩ := andB_split h
  obtain ⟨h7, h⟩ := andB_split h
  obtain ⟨hup, h⟩ := andB_split h
  obtain ⟨hdg, hone⟩ := andB_split h
  refine ⟨Nat.eq_of_beq_eq_true hc, ?_, Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1,
    Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7,
    Nat.eq_of_beq_eq_true hup, Nat.eq_of_beq_eq_true hdg, Nat.eq_of_beq_eq_true hone⟩
  rw [Nat.eq_of_beq_eq_true hrm]
  change 1 <<< 248 - 1 = _
  rw [Nat.one_shiftLeft]

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

theorem pkMat_mulB (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (A B : ℕ) : pkMat (mulB c rm A B) = pkMat A * pkMat B := by
  obtain ⟨hc, hrm, -⟩ := consts_spec h
  subst hc hrm
  exact pkMat_mulB_rep A B

theorem inLayout_mulB (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (A B : ℕ) : InLayout (mulB c rm A B) := by
  obtain ⟨hc, hrm, -⟩ := consts_spec h
  subst hc hrm
  exact inLayout_mulB_rep A B

theorem pkMat_trB (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (A : ℕ) : pkMat (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 A) = (pkMat A).transpose := by
  obtain ⟨-, -, h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := consts_spec h
  subst h0 h1 h2 h3 h4 h5 h6 h7
  exact pkMat_trB_rep A

theorem inLayout_trB (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {A : ℕ} (hA : InLayout A) : InLayout (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 A) := by
  obtain ⟨-, -, h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := consts_spec h
  subst h0 h1 h2 h3 h4 h5 h6 h7
  exact inLayout_trB_rep hA

theorem pkMat_one (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true) :
    pkMat ONE = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdg, hone⟩ := consts_spec h
  rw [hone, hdg]
  exact pkMat_dg

theorem inLayout_one (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true) :
    InLayout ONE := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdg, hone⟩ := consts_spec h
  rw [hone, hdg]
  exact inLayout_dg

theorem pkMat_powB (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (M e nb : ℕ) (he : e < 2 ^ nb) : pkMat (powB c rm ONE M e nb) = pkMat M ^ e := by
  have h1 := pkMat_one h
  obtain ⟨hc, hrm, -⟩ := consts_spec h
  subst hc hrm
  exact pkMat_powB_rep ONE M e nb h1 he

theorem pkVec_vecB (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (v M : ℕ) : pkVec (vecB rm v M) = Matrix.vecMul (pkVec v) (pkMat M) := by
  obtain ⟨-, hrm, -⟩ := consts_spec h
  subst hrm
  exact pkVec_vecB_rep v M

theorem pkVec_rowB (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (G : ℕ) (r : Fin 248) : pkVec (rowB rm G r.val) = fun j => pkMat G r j := by
  obtain ⟨-, hrm, -⟩ := consts_spec h
  subst hrm
  funext j
  have hj := j.isLt
  rw [pkVec_apply, pkMat_apply]
  have e : (rowB (2 ^ 248 - 1) G r.val).testBit j.val = G.testBit (256 * r.val + j.val) := by
    change ((G >>> (r.val * 256)) &&& (2 ^ 248 - 1)).testBit j.val = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
      show r.val * 256 + j.val = 256 * r.val + j.val by omega]
    simp [hj]
  rw [e]

theorem vecB_lt (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (v M : ℕ) : vecB rm v M < 2 ^ 248 := by
  obtain ⟨-, hrm, -⟩ := consts_spec h
  subst hrm
  exact vecB_lt_rep v M

theorem chkUni_spec (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {M : ℕ} (hM : chkUni up dg M = true) :
    (∀ i j : Fin 248, i < j → pkMat M i j = 0) ∧ ∀ i : Fin 248, pkMat M i i = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hup, hdg, -⟩ := consts_spec h
  subst hup hdg
  exact chkUni_rep hM

theorem pkMat_wordAB_zero (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (A B Bi w : ℕ) : pkMat (wordAB c rm ONE A B Bi w 0) = 1 :=
  pkMat_one h

theorem pkMat_wordAB_succ (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (A B Bi w n : ℕ) :
    pkMat (wordAB c rm ONE A B Bi w (n + 1)) =
      pkMat (wordAB c rm ONE A B Bi w n) * pkMat (wordLetter A B Bi (bitsN w (2 * n) 2)) := by
  rw [wordAB_succ, pkMat_mulB h]

theorem inLayout_wordAB (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (A B Bi w : ℕ) : ∀ n, InLayout (wordAB c rm ONE A B Bi w n)
  | 0 => inLayout_one h
  | n + 1 => by
    rw [wordAB_succ]
    exact inLayout_mulB h _ _

theorem inLayout_powB (h : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (M e nb : ℕ) : InLayout (powB c rm ONE M e nb) := by
  have h1 := inLayout_one h
  obtain ⟨hc, hrm, -⟩ := consts_spec h
  subst hc hrm
  rw [powB_eq_powBn]
  exact inLayout_powBn ONE M e nb h1 nb

end Consts

end CFSG.KC.Th.Spec

end
