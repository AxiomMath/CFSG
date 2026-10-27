module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM

public section

namespace CFSG.ComponentClassification.HSFLit

open Sec8

namespace KD8ab

@[expose] def inCt (a : MA) : Bool := decide (a * MA.t = MA.t * a)

@[expose] def Ct : Subgroup MA := MA.ofPred inCt (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem mem_Ct {a : MA} : a ∈ Ct ↔ a * MA.t = MA.t * a := by
  change inCt a = true ↔ _
  simp [inCt]

theorem card_Ct : Nat.card Ct = 32 := by
  rw [Ct, MA.card_ofPred]; decide +kernel

theorem Ct_T1 : ∀ a : MA, a * MA.t = MA.t * a → MA.inT1 a = true := by decide +kernel

theorem not_conj_tu_zt : ∀ a : MA, a * (MA.t * MA.u) * a⁻¹ ≠ MA.t ∧
    a * (MA.t * MA.u) * a⁻¹ ≠ MA.z * MA.t := by decide +kernel

theorem dc_fix_zk : ∀ e : Bool, ∀ c₂ ∈ [1, MA.z], ∀ a ∈ MA.ZList, dc e c₂ a = a →
    a = 1 ∨ a = MA.z := by decide +kernel

@[expose] def Z2List : List MA :=
  [1, MA.z, MA.k, MA.z * MA.k, MA.w₁, MA.z * MA.w₁, MA.k * MA.w₁, MA.z * MA.k * MA.w₁]

theorem comm_w₁_iff : ∀ a : MA, a * MA.w₁ = MA.w₁ * a ↔ MA.inM a = true := by decide +kernel

end KD8ab

end CFSG.ComponentClassification.HSFLit
