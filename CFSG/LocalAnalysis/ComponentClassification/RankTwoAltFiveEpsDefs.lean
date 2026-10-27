module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveSylow

public section

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.ComponentClassification.RankTwoAltFive

@[expose] def Asc310EpsOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (T V₀ : Subgroup G),
    Setting310 A R g T V₀ → rankTwoX A = ⊤ → IsSimpleGroup G →
    ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G) →
    ∀ P : Subgroup G, IsSylowOf 2 P (transvGroup (R ⊔ T) V₀) → R ⊔ T ≤ P →
      P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T → Nat.card P = 64 →
        EpsOne (R ⊔ T) P

end CFSG.ComponentClassification.RankTwoAltFive
