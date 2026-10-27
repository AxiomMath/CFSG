module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open Bender

theorem nestedAt_of_isBenderGroup {X : Type*} [Group X] [Finite X] (hX : fusionIsBenderGroup X)
    (T : Sylow 2 X) : NestedAt (T : Subgroup X) := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact nestedAt_of_mulEquiv_psl2 hf e T
  · exact nestedAt_of_mulEquiv_psu3 hf e T
  · exact nestedAt_of_mulEquiv_sz ha e T

theorem bender_strongly_closed_union_nested {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.fusionIsBenderGroup X) (T : Sylow 2 X) (A₁ A₂ : Subgroup X)
    (h₁ : A₁ ≤ (T : Subgroup X)) (h₂ : A₂ ≤ (T : Subgroup X)) (hc : ⁅A₁, A₂⁆ = ⊥)
    (hcl : ∀ a ∈ (A₁ : Set X) ∪ A₂, ∀ x : X, x⁻¹ * a * x ∈ (T : Subgroup X) →
      x⁻¹ * a * x ∈ (A₁ : Set X) ∪ A₂) :
    A₁ ≤ A₂ ∨ A₂ ≤ A₁ :=
  nestedAt_of_isBenderGroup hX T A₁ A₂ h₁ h₂ hc hcl

end CFSG.ComponentClassification.AschbacherToolkit
