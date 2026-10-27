module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Matrix

section Matrices

variable {F : Type} [Field F]

theorem sl2c_cayley_hamilton (A : Matrix (Fin 2) (Fin 2) F) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sl2c_eq_one_of_sq_eq {A : Matrix (Fin 2) (Fin 2) F}
    (hA : A * A = (2 : F) • A - (1 : Matrix (Fin 2) (Fin 2) F)) {m : ℕ} (hm : (m : F) ≠ 0)
    (h : A ^ m = 1) : A = 1 := by
  set N : Matrix (Fin 2) (Fin 2) F := A - 1 with hN
  have hNN : N * N = 0 := by
    rw [hN, sub_mul, mul_sub, mul_sub, hA, mul_one, one_mul, mul_one]
    simp only [two_smul]
    abel
  have hAN : A = 1 + N := by rw [hN]; abel
  have h1 : ∀ k : ℕ, (1 + N) ^ k = 1 + (k : F) • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      have e : (1 + (k : F) • N) * (1 + N) =
          1 + ((k : F) + 1) • N + (k : F) • (N * N) := by
        simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, add_smul,
          one_smul]
        abel
      rw [e, hNN, smul_zero, add_zero, Nat.cast_succ]
  rw [hAN, h1] at h
  have h2 : (m : F) • N = 0 := by
    have := congrArg (fun X => X - 1) h
    simpa using this
  have : N = 0 := (smul_eq_zero.mp h2).resolve_left hm
  rw [hAN, this, add_zero]

theorem sl2c_exists_cyclic_vector (A : Matrix (Fin 2) (Fin 2) F) (hA : ∀ c : F, A ≠ c • 1) :
    ∃ v : Fin 2 → F, v 0 * (A *ᵥ v) 1 - (A *ᵥ v) 0 * v 1 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := hcon ![1, 0]
  have h2 := hcon ![0, 1]
  have h3 := hcon ![1, 1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2 h3
  apply hA (A 0 0)
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | exact h2 | exact h1 | linear_combination h3 - h1 + h2

theorem sl2c_mul_companion (g : Matrix (Fin 2) (Fin 2) F) (hdet : g.det = 1) (v : Fin 2 → F) :
    g * !![v 0, (g *ᵥ v) 0; v 1, (g *ᵥ v) 1] =
      !![v 0, (g *ᵥ v) 0; v 1, (g *ᵥ v) 1] * !![0, -1; 1, g.trace] := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  · linear_combination (-(v 0)) * hdet
  · linear_combination (-(v 1)) * hdet

end Matrices

end CFSG.GH74.GLS.Stage4.Rest
