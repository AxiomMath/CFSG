module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open Matrix
open scoped commutatorElement

theorem commutator_conjAut_fieldAut {F : Type} [Field F] {n : ℕ} {σ : F ≃+* F}
    {A : GL (Fin n) F} :
    ⁅conjAut n F A, fieldAut n F σ⁆ =
      conjAut n F (A * GeneralLinearGroup.map (σ : F →+* F) A⁻¹) := by
  rw [commutatorElement_def]
  rw [show (conjAut n F A)⁻¹ = conjAut n F A⁻¹ by rw [← map_inv]]
  rw [show (fieldAut n F σ)⁻¹ = fieldAut n F σ⁻¹ by rw [← map_inv]]
  rw [show conjAut n F A * fieldAut n F σ * conjAut n F A⁻¹ * fieldAut n F σ⁻¹ =
      (conjAut n F A * fieldAut n F σ) * (conjAut n F A⁻¹ * fieldAut n F σ⁻¹) by group]
  rw [conjAut_mul_fieldAut_mul]
  rw [mul_inv_cancel, map_one, mul_one]

end CFSG.LocalAnalysis.ComponentInitial.LinearFlag

end
