module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

@[expose] def HeldKInvariantComponentStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L →
    ∀ (a u : X) (J : Subgroup X), orderOf a = 2 → L ≤ centralizer ({a} : Set X) →
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) → HeldTwoA L u →
      IsComponent ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))) →
      J ≤ centralizer ({u} : Set X) → IsComponent (J.subgroupOf (centralizer ({u} : Set X))) →
      J ≠ gsFixedLayer L u → Nonempty (↥J ≃* ↥(gsFixedLayer L u)) → conjugate J a = J →
      a ∉ centralizer (J : Set X) → False

end CFSG.ComponentClassification.GrSLit
