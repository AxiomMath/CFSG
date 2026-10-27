module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def HeldSingleNormalStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldSetting X L →
    ∀ S : Subgroup X, IsSylowTwoIn S (normalizer (L : Set X)) →
    ∀ W : Subgroup X, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup X, B ≤ S → IsElemTwo B → Nat.card B = 8 → wGroup B = W) →
      normalizer (L : Set X) ≤ normalizer (W : Set X) →
    ∀ K : Subgroup X, K ≤ normalizer (W : Set X) →
      IsPComponent 2 (K.subgroupOf (normalizer (W : Set X))) →
      L ⊔ oddIn (normalizer (W : Set X)) = K ⊔ oddIn (normalizer (W : Set X)) →
      normalizer (W : Set X) ≤ normalizer (K : Set X)

end CFSG.ComponentClassification.GrSLit
