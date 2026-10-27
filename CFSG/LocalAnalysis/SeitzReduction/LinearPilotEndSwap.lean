module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem false_of_simple_of_swapFactors {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {t : G} (ht : orderOf t = 2) {G₁ G₀ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hsup : G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  subst hsup
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple ht hq h₁₂ rfl huniq

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type}
  [Field K] [Finite K] [CharP K 2]

end CFSG.SeitzReduction.LinearPilot
