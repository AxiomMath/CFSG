module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open scoped Kronecker

variable {F : Type*} [Field F] [CharP F 2] {n : ℕ}

omit [CharP F 2] in
@[simp]
theorem map_one_kronecker_map_one (σ : F ≃+* F) :
    (1 : Matrix (Fin n) (Fin n) F) ⊗ₖ ((1 : Matrix (Fin n) (Fin n) F).map σ) = 1 := by
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.one_kronecker_one]

theorem sub_one_mul_sub_one_eq_zero_of_mul_self (x : Matrix (Fin n) (Fin n) F)
    (hx : x * x = 1) : (x - 1) * (x - 1) = 0 := by
  by_cases hn : Nonempty (Fin n)
  · have := hn
    rw [CharTwo.sub_eq_add]
    have h : (x + 1) * (x + 1) = (x * x + 1) + (x + x) := by noncomm_ring
    rw [h, hx]
    simp [CharTwo.add_self_eq_zero]
  · have : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    exact Subsingleton.elim _ _

theorem eq_one_of_eq_smul_one_of_mul_self (x : Matrix (Fin n) (Fin n) F) (hx : x * x = 1)
    (hsc : ∃ c : F, x = c • 1) : x = 1 := by
  obtain ⟨c, rfl⟩ := hsc
  by_cases hn : Nonempty (Fin n)
  · obtain ⟨i⟩ := hn
    have hdiag : (c • (1 : Matrix (Fin n) (Fin n) F)) * (c • 1) =
        diagonal (fun _ : Fin n => c * c) := by
      rw [Matrix.smul_eq_diagonal_mul, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    have hsq : c * c = 1 := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i i) hx
      rw [hdiag] at h
      simpa using h
    have hc : c = 1 := by
      have h : (c - 1) * (c - 1) = 0 := by
        rw [CharTwo.sub_eq_add]
        have h' : (c + 1) * (c + 1) = (c * c + 1) + (c + c) := by ring
        rw [h', hsq]
        simp [CharTwo.add_self_eq_zero]
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h)
    rw [hc, one_smul]
  · have : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    exact Subsingleton.elim _ _

end CFSG.LieType.SpecialLinear
