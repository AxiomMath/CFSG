module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34SquareCenterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    ∀ u ∈ P, u * u ∈ zStarIn J → ∃ z ∈ P ⊓ zStarIn J, u * u = z * z

@[expose] def L34EightsConnectedFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    ¬ IsCyclic ↥(P ⊓ zStarIn J) → (∃ z ∈ P ⊓ zStarIn J, z * z ≠ 1) →
    ∀ E F : Subgroup G, E ≤ P → F ≤ P → IsEightGroup E → IsEightGroup F →
      ∃ j ∈ J, AbelianConnectedIn J 3 E (conjugate F j)

end CFSG.ComponentClassification.GrSLit
