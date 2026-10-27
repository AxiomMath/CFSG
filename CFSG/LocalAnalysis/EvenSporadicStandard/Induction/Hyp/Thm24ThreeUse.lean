module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78

@[expose] def Thm24ThreeUse (s' : TauCeti.SporadicName) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ∀ A : Subgroup H, SolStd A →
      OddCover s' A → 2 ≤ CFSG.pRank 2 ↥(centralizer (A : Set H)) → False

end CFSG.EvenSporadicStandard.Induction.Hyp
