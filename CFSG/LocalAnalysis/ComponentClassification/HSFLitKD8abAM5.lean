module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM3

public section

namespace CFSG.ComponentClassification.HSFLit

open Sec8

namespace KD8ab

theorem z2_conj : ∀ c₂ ∈ [1, MA.z], ∀ a : MA,
    (∀ h ∈ MA.gens, h * a * h⁻¹ = a ∨ h * a * h⁻¹ = MA.z * a) →
    MA.inT1 a = true ∧ ((dc false c₂ a = a ∨ dc false c₂ a = MA.z * a) →
      (pAct false c₂ a = a ∨ pAct false c₂ a = MA.z * a) → a ∈ Z2List) := by
  decide +kernel

theorem conj_w₁_all : ∀ b : MA, b * MA.w₁ * b⁻¹ = MA.w₁ ∨ b * MA.w₁ * b⁻¹ = MA.z * MA.w₁ := by
  decide +kernel

theorem t_conj_w₁ : MA.t * MA.w₁ * MA.t⁻¹ = MA.z * MA.w₁ := by decide +kernel

theorem t_conj_k : MA.t * MA.k * MA.t⁻¹ = MA.k := by decide +kernel

theorem noinv : ∀ c₂ ∈ [1, MA.z], ∀ b : MA, MA.inT1 b = true →
    b * dc true c₂ b * tE true ≠ 1 ∧
      MA.w₂ * b * dc true c₂ b * (tE true * MA.w₂ * tE true) * tE true ≠ 1 := by
  decide +kernel

theorem sq_M : ∀ a : MA, MA.inM (a * a) = true := by decide +kernel

theorem inM_t_mul : ∀ a : MA, MA.inM (MA.t * a) = !MA.inM a := by decide +kernel

theorem t_mul_t : MA.t * MA.t = 1 := by decide +kernel

theorem zkw_facts : MA.z * MA.z = 1 ∧ MA.k * MA.k = 1 ∧ MA.w₁ * MA.w₁ = 1 ∧
    MA.k * MA.w₁ = MA.w₁ * MA.k ∧ MA.z ≠ 1 ∧ MA.k ≠ 1 ∧ MA.k ≠ MA.z ∧ MA.w₁ ≠ 1 ∧
    MA.w₁ ≠ MA.z ∧ MA.w₁ ≠ MA.k ∧ MA.w₁ ≠ MA.z * MA.k := by decide +kernel

theorem ZList_T1 : ∀ c ∈ MA.ZList, MA.inT1 c = true := by decide +kernel

end KD8ab

end CFSG.ComponentClassification.HSFLit
