module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM

public section

namespace CFSG.ComponentClassification.HSFLit

open Sec8

namespace KD8ab
@[expose] def qh : MA := MA.u * MA.y * MA.k
theorem qh_facts : qh * qh = MA.z ∧ qh * MA.t = MA.t * qh ∧ qh * MA.w₁ = MA.w₁ * qh ∧
    MA.inT1 qh = true := by decide +kernel
theorem dc_qh : ∀ c₂ ∈ [1, MA.z], dc false c₂ qh = qh := by decide +kernel
theorem cobound : ∀ c₂ ∈ [1, MA.z], ∀ a : MA, MA.inT1 a = true → a * dc false c₂ a = 1 →
    a * MA.w₁ = MA.w₁ * a → ∃ s : MA, MA.inT1 s = true ∧ a = s⁻¹ * dc false c₂ s := by
  decide +kernel
theorem cert_e : ∀ c₂ ∈ [1, MA.z], ∀ ζ ∈ MA.ZList,
    pAct false c₂ (dc false c₂ (MA.w₂ * (MA.condWit 1 * ζ))) = MA.w₂ * (MA.condWit 1 * ζ) →
    ∃ r ∈ [MA.v, MA.u * MA.v * MA.y],
      pAct false c₂ (dc false c₂ r) * (MA.w₂ * (MA.w₂ * (MA.condWit 1 * ζ))) = MA.w₂ * r ∧
      MA.w₂ * r * pAct false c₂ qh = qh * (MA.w₂ * r) := by decide +kernel
end KD8ab

end CFSG.ComponentClassification.HSFLit
