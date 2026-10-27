module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34NoFrobeniusFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J E : Subgroup G) (h : G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → E ≤ normalizer (J : Set G) → IsEightGroup E →
    E ⊓ coreActionKernel J = ⊥ → h ∈ normalizer (J : Set G) → h ∈ normalizer (E : Set G) →
    ∃ e ∈ E, e ≠ 1 ∧ h * e = e * h

end CFSG.ComponentClassification.GrSLit
