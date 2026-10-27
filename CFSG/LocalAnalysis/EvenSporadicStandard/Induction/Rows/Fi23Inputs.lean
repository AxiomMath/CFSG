module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def Fi23TwoSylow : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi23 L →
      SolomonGlobalQ H L K t u → fiIn23 H L K u →
        ∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2

end CFSG.EvenSporadicStandard.Induction
