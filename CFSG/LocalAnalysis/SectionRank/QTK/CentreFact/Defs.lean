module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup

@[expose] def OddBound (r : ℕ) (S : Type) [Group S] [Finite S] : Prop :=
  ∀ R : Subgroup S, R ≠ ⊥ → IsPGroup 2 R → CFSG.Open.pRank r (normalizer (R : Set S)) ≤ 2

@[expose] def QTCentreFactSub : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.evenRank G ≤ 2 → ∀ Y : Subgroup G,
    CFSG.IsQuasisimple ↥Y → CFSG.SectionRank.IsKGroupCat ↥Y → ∀ r : ℕ, r.Prime → r ≠ 2 →
      r ∣ Nat.card (center ↥Y) → OddBound r (↥Y ⧸ center ↥Y)

end CFSG.SectionRank.QTK.CentreFact
