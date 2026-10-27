module

public import CFSG.Adapters.Involutions
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherTheorem3

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem commute_of_isolated (hO : CFSG.oddCore Γ = ⊥) (S : Sylow 2 Γ) {z : Γ}
    (hzS : z ∈ (S : Subgroup Γ)) (hzc : ∀ s ∈ (S : Subgroup Γ), s * z = z * s)
    (hz2 : orderOf z = 2)
    (hiso : ∀ g : Γ, g⁻¹ * z * g ∈ (S : Subgroup Γ) → g⁻¹ * z * g = z) (g : Γ) :
    g * z = z * g := by
  set z' : (S : Subgroup Γ) := ⟨z, hzS⟩
  have hzZ : z' ∈ center (S : Subgroup Γ) := by
    rw [mem_center_iff]
    intro s
    exact Subtype.ext (hzc s s.2)
  have hz' : orderOf z' = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  obtain ⟨h1, -⟩ := CFSG.Adapters.glauberman_zStar S z' hzZ hz' hiso
  obtain ⟨c, hc, k, hk, rfl⟩ := h1 g
  rw [hO, mem_bot] at hk
  rw [hk, mul_one]
  exact mem_centralizer_singleton_iff.mp hc

end CFSG.ComponentClassification.GMS78
