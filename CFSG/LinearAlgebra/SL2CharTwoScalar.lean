module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LinearAlgebra

theorem exists_specialLinear_conj_eq_of_det_ne_zero {K : Type*} [Field K] [Finite K] [CharP K 2]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) :
    ∃ (s : Matrix.SpecialLinearGroup (Fin 2) K) (μ : K), μ ≠ 0 ∧
      M = μ • (s : Matrix (Fin 2) (Fin 2) K) ∧
      ∀ A : Matrix (Fin 2) (Fin 2) K,
        M * A * M⁻¹ = (s : Matrix (Fin 2) (Fin 2) K) * A *
          (s : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (R := K) M.det
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hM
    rw [hμ]
    ring
  let sMat : Matrix (Fin 2) (Fin 2) K := μ⁻¹ • M
  have hsdet : sMat.det = 1 := by
    change (μ⁻¹ • M).det = 1
    rw [Matrix.det_smul, hμ, Fintype.card_fin]
    field_simp [hμ0]
  let s : Matrix.SpecialLinearGroup (Fin 2) K := ⟨sMat, hsdet⟩
  have hMs : M = μ • (s : Matrix (Fin 2) (Fin 2) K) := by
    dsimp only [s, sMat]
    rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have hsunit : IsUnit (s : Matrix (Fin 2) (Fin 2) K).det := by
    change IsUnit sMat.det
    rw [hsdet]
    exact isUnit_one
  have hMinv : M⁻¹ = μ⁻¹ • (s : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
    letI : Invertible μ := invertibleOfNonzero hμ0
    rw [hMs]
    simpa using Matrix.inv_smul ((s : Matrix (Fin 2) (Fin 2) K)) μ hsunit
  refine ⟨s, μ, hμ0, hMs, fun A => ?_⟩
  rw [hMinv, hMs, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ hμ0, one_smul]

end CFSG.LinearAlgebra
