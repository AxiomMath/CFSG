module

public import Certificates.Data.Kernel.Sp43K
public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.CodeSound

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43

@[expose] def val2 (p m n : ℕ) : ZMod 3 := if p.testBit n then 1 else if m.testBit n then 2 else 0

@[expose] def ExT (c : ℕ) : Prop := ∀ n < 16, (c.testBit n && c.testBit (n + 16)) = false

@[expose] def toMT (c : ℕ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  fun x y => val2 c (c >>> 16) (4 * ix x + ix y)

theorem testBit_laneT {n : ℕ} (hn : n < 16) : laneT.testBit n = true := by
  have e : laneT = 2 ^ 16 - 1 := rfl
  rw [e, Nat.testBit_two_pow_sub_one]
  simpa using hn

theorem val_mul3 {ap am bp bm n : ℕ} (ha : (ap.testBit n && am.testBit n) = false)
    (hb : (bp.testBit n && bm.testBit n) = false) :
    val2 (mul3P ap am bp bm) (mul3M ap am bp bm) n = val2 ap am n * val2 bp bm n ∧
      ((mul3P ap am bp bm).testBit n && (mul3M ap am bp bm).testBit n) = false := by
  simp only [val2, mul3P, mul3M, Nat.testBit_or, Nat.testBit_and]
  revert ha hb
  generalize ap.testBit n = x1
  generalize am.testBit n = x2
  generalize bp.testBit n = x3
  generalize bm.testBit n = x4
  decide +revert

theorem val_add3 {ap am bp bm n : ℕ} (hn : n < 16) (ha : (ap.testBit n && am.testBit n) = false)
    (hb : (bp.testBit n && bm.testBit n) = false) :
    val2 (add3P ap am bp bm) (add3M ap am bp bm) n = val2 ap am n + val2 bp bm n ∧
      ((add3P ap am bp bm).testBit n && (add3M ap am bp bm).testBit n) = false := by
  simp only [val2, add3P, add3M, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
    testBit_laneT hn]
  revert ha hb
  generalize ap.testBit n = x1
  generalize am.testBit n = x2
  generalize bp.testBit n = x3
  generalize bm.testBit n = x4
  decide +revert

theorem testBit_4369 : ∀ n < 16, Nat.testBit 4369 n = decide (n % 4 = 0) := by decide

theorem testBit_15 : ∀ n < 16, Nat.testBit 15 n = decide (n < 4) := by decide

theorem testBit_colT (x : ℕ) {i j k : ℕ} (hi : i < 4) (hj : j < 4) (hk : k < 4) :
    (colT x k).testBit (4 * i + j) = x.testBit (4 * i + k) := by
  interval_cases i <;> interval_cases j <;> interval_cases k <;>
    simp [colT, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      testBit_4369]

theorem testBit_rowT (x : ℕ) {i j k : ℕ} (hi : i < 4) (hj : j < 4) (hk : k < 4) :
    (rowT x k).testBit (4 * i + j) = x.testBit (4 * k + j) := by
  interval_cases i <;> interval_cases j <;> interval_cases k <;>
    simp [rowT, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      testBit_15]

theorem testBit_low (a : ℕ) {n : ℕ} (hn : n < 16) : (a &&& laneT).testBit n = a.testBit n := by
  rw [Nat.testBit_and, testBit_laneT hn, Bool.and_true]

theorem testBit_high (a n : ℕ) : (a >>> 16).testBit n = a.testBit (n + 16) := by
  rw [Nat.testBit_shiftRight, Nat.add_comm]

theorem val_term {a b i j k : ℕ} (ha : ExT a) (hb : ExT b) (hi : i < 4) (hj : j < 4)
    (hk : k < 4) :
    val2 (termP a b k) (termM a b k) (4 * i + j) =
        val2 a (a >>> 16) (4 * i + k) * val2 b (b >>> 16) (4 * k + j) ∧
      ((termP a b k).testBit (4 * i + j) && (termM a b k).testBit (4 * i + j)) = false := by
  have hA : ((colT (a &&& laneT) k).testBit (4 * i + j) &&
      (colT (a >>> 16) k).testBit (4 * i + j)) = false := by
    rw [testBit_colT _ hi hj hk, testBit_colT _ hi hj hk, testBit_low _ (by omega), testBit_high]
    exact ha _ (by omega)
  have hB : ((rowT (b &&& laneT) k).testBit (4 * i + j) &&
      (rowT (b >>> 16) k).testBit (4 * i + j)) = false := by
    rw [testBit_rowT _ hi hj hk, testBit_rowT _ hi hj hk, testBit_low _ (by omega), testBit_high]
    exact hb _ (by omega)
  obtain ⟨e, hx⟩ := val_mul3 hA hB
  refine ⟨?_, hx⟩
  rw [termP, termM, e]
  simp only [val2, testBit_colT _ hi hj hk, testBit_rowT _ hi hj hk,
    testBit_low _ (by omega : 4 * i + k < 16), testBit_low _ (by omega : 4 * k + j < 16)]

theorem val_s3 {a b i j : ℕ} (ha : ExT a) (hb : ExT b) (hi : i < 4) (hj : j < 4) :
    val2 (s3P a b) (s3M a b) (4 * i + j) =
        val2 a (a >>> 16) (4 * i + 0) * val2 b (b >>> 16) (4 * 0 + j) +
          val2 a (a >>> 16) (4 * i + 1) * val2 b (b >>> 16) (4 * 1 + j) +
          val2 a (a >>> 16) (4 * i + 2) * val2 b (b >>> 16) (4 * 2 + j) +
          val2 a (a >>> 16) (4 * i + 3) * val2 b (b >>> 16) (4 * 3 + j) ∧
      ((s3P a b).testBit (4 * i + j) && (s3M a b).testBit (4 * i + j)) = false := by
  have hn : 4 * i + j < 16 := by omega
  obtain ⟨e0, x0⟩ := val_term (k := 0) ha hb hi hj (by norm_num)
  obtain ⟨e1, x1⟩ := val_term (k := 1) ha hb hi hj (by norm_num)
  obtain ⟨e2, x2⟩ := val_term (k := 2) ha hb hi hj (by norm_num)
  obtain ⟨e3, x3⟩ := val_term (k := 3) ha hb hi hj (by norm_num)
  obtain ⟨f1, y1⟩ := val_add3 hn x0 x1
  obtain ⟨f2, y2⟩ := val_add3 hn y1 x2
  obtain ⟨f3, y3⟩ := val_add3 hn y2 x3
  refine ⟨?_, y3⟩
  simp only [s3P, s3M, s2P, s2M, s1P, s1M]
  rw [f3, f2, f1, e0, e1, e2, e3]

theorem testBit_mulT_low (a b : ℕ) {n : ℕ} (hn : n < 16) :
    (mulT a b).testBit n = (s3P a b).testBit n := by
  have h : ¬ 16 ≤ n := by omega
  simp [mulT, Nat.testBit_or, testBit_low _ hn, Nat.testBit_shiftLeft, h]

theorem testBit_mulT_high (a b n : ℕ) : (mulT a b).testBit (n + 16) = (s3M a b).testBit n := by
  have e : laneT = 2 ^ 16 - 1 := rfl
  rw [mulT, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, e,
    Nat.testBit_two_pow_sub_one]
  simp

private theorem ix_lt' (a : Fin 2 ⊕ Fin 2) : ix a < 4 := by
  rcases a with i | i <;> simp only [ix] <;> omega

theorem toMT_mulT {a b : ℕ} (ha : ExT a) (hb : ExT b) : toMT (mulT a b) = toMT a * toMT b := by
  ext x y
  have hi := ix_lt' x
  have hj := ix_lt' y
  have hn : 4 * ix x + ix y < 16 := by omega
  have e : toMT (mulT a b) x y = val2 (s3P a b) (s3M a b) (4 * ix x + ix y) := by
    simp only [toMT, val2, testBit_mulT_low a b hn, testBit_high, testBit_mulT_high]
  rw [e, (val_s3 ha hb hi hj).1, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp only [toMT, ix, Fin.val_zero, Fin.val_one, Nat.add_zero, Nat.mul_zero, Nat.zero_add,
    Nat.mul_one]
  abel

theorem toMT_oneT : toMT oneT = 1 := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;> decide

theorem exT_oneT : ExT oneT := by
  unfold ExT
  decide

theorem exT_mulT {a b : ℕ} (ha : ExT a) (hb : ExT b) : ExT (mulT a b) := by
  intro n hn
  rw [testBit_mulT_low a b hn, testBit_mulT_high]
  have e : n = 4 * (n / 4) + n % 4 := by omega
  rw [e]
  exact (val_s3 ha hb (by omega) (by omega)).2

end CFSG.KC.Sp43K

end
