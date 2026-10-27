module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.LyonsUnitaryFour

abbrev LyonsRow : Type := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ

namespace LyonsRow

instance instDecidableEq : DecidableEq LyonsRow := instDecidableEqProd

instance instDecidableEqMultiset : DecidableEq (Multiset LyonsRow) :=
  Multiset.decidableEq

@[expose] def fourierSum : LyonsRow → ℤ
  | (_, a, b, c, d, e) => a + b + c + d + e

@[expose] def strictContribution : LyonsRow → ℤ
  | (t, a, b, c, d, e) =>
    4 * t ^ 2 + 16 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) - 3 * (a + b + c + d + e) ^ 2

@[expose] def rotate : LyonsRow → LyonsRow
  | (t, a, b, c, d, e) => (t, a, e, b, c, d)

@[expose] def reflect : LyonsRow → LyonsRow
  | (t, a, b, c, d, e) => (t, a, b, e, d, c)

@[expose] def toVec : LyonsRow → Fin 6 → ℤ
  | (t, a, b, c, d, e) => ![t, a, b, c, d, e]

structure Admissible (r : LyonsRow) : Prop where
  fourierSum_pos : 0 < r.fourierSum
  modEq : r.1 ≡ r.fourierSum [ZMOD 4]
  strictContribution_lt : r.strictContribution < 64

theorem rotate_injective : Function.Injective rotate := by
  rintro ⟨t, a, b, c, d, e⟩ ⟨t', a', b', c', d', e'⟩ h
  simp only [rotate, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

theorem rotate_rotate_rotate_rotate (r : LyonsRow) : r.rotate.rotate.rotate.rotate = r := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  rfl

theorem toVec_rotate (r : LyonsRow) (i : Fin 6) :
    r.rotate.toVec i = r.toVec (![0, 1, 5, 2, 3, 4] i) := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  fin_cases i <;> rfl

end LyonsRow

@[expose] def lyonsGram : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j =>
    if i = 0 ∨ j = 0 then (if i = j then 16 else 0) else 4 * (if i = j then 1 else 0) + 12

@[expose] def gramSum (M : Multiset LyonsRow) : Matrix (Fin 6) (Fin 6) ℤ :=
  (M.map fun r => Matrix.vecMulVec r.toVec r.toVec).sum

@[expose] def principalRow : LyonsRow := (1, 1, 0, 0, 0, 0)

structure LyonsColumnConditions (M : Multiset LyonsRow) : Prop where
  admissible : ∀ r ∈ M, r.Admissible
  gramSum_eq : gramSum M = lyonsGram
  map_rotate : M.map LyonsRow.rotate = M

theorem gramSum_apply (M : Multiset LyonsRow) (i j : Fin 6) :
    gramSum M i j = (M.map fun r => r.toVec i * r.toVec j).sum := by
  induction M using Multiset.induction_on with
  | empty => simp [gramSum]
  | cons r M ih =>
    simp only [gramSum, Multiset.map_cons, Multiset.sum_cons, Matrix.add_apply,
      Matrix.vecMulVec_apply] at ih ⊢
    rw [ih]

theorem count_rotate_of_map_rotate {M : Multiset LyonsRow} (hM : M.map LyonsRow.rotate = M)
    (r : LyonsRow) : M.count r.rotate = M.count r := by
  conv_lhs => rw [← hM]
  exact Multiset.count_map_eq_count' _ _ LyonsRow.rotate_injective r

end CFSG.LyonsUnitaryFour
