module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

@[expose] def Lemma212Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), L ∈ solomonKStar G → S ≠ ⊥ →
    IsPGroup 2 S → S ≤ coreActionKernel L →
    twoLayerIn (L ⊓ centralizer (S : Set G)) ≤ solomonKStarOf (centralizer (S : Set G))

end CFSG.ComponentClassification.Sol76
