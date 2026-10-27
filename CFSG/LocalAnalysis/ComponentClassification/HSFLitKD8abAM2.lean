module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM

public section

namespace CFSG.ComponentClassification.HSFLit

open Sec8

namespace KD8ab

theorem pAct_w₂ : ∀ e : Bool, ∀ c₂ ∈ [1, MA.z], ∀ a : MA, MA.inT1 a = true →
    pAct e c₂ (MA.w₂ * pAct e c₂ a * MA.w₂⁻¹) =
      MA.condWit (cOne e) * a * (MA.condWit (cOne e))⁻¹ := by decide +kernel

theorem pAct_pAct : ∀ e : Bool, ∀ c₂ ∈ [1, MA.z], ∀ a : MA, MA.inT1 a = true →
    pAct e c₂ (pAct e c₂ a) = a := by decide +kernel

theorem tE_inv (e : Bool) : (tE e)⁻¹ = tE e := by cases e <;> decide +kernel

theorem tE_mul_tE (e : Bool) : tE e * tE e = 1 := by cases e <;> decide +kernel

theorem dc_tE : ∀ e : Bool, ∀ c₂ ∈ [1, MA.z], ∀ ζ ∈ MA.ZList,
    dc e c₂ (tE e * ζ) = tE e * ζ → ζ = 1 ∨ ζ = MA.z := by decide +kernel

theorem not_conj_y_u : ∀ s : MA, s * MA.t = MA.t * s → s * MA.y * s⁻¹ ≠ MA.u := by
  decide +kernel

theorem gens7_T1 : ∀ g ∈ gens7, MA.inT1 g = true := by decide +kernel

theorem dc_T1 : ∀ e : Bool, ∀ c₂ ∈ [1, MA.z], ∀ a : MA, MA.inT1 (dc e c₂ a) = true := by
  decide +kernel

theorem dci_T1 : ∀ e : Bool, ∀ c₂ ∈ [1, MA.z], ∀ a : MA, MA.inT1 (dci e c₂ a) = true := by
  decide +kernel

theorem pAct_T1 : ∀ e : Bool, ∀ c₂ ∈ [1, MA.z], ∀ a : MA, MA.inT1 (pAct e c₂ a) = true := by
  decide +kernel

end KD8ab

end CFSG.ComponentClassification.HSFLit
