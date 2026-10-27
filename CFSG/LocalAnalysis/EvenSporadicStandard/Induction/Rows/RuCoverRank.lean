module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuFamilyNotExc

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

@[expose] def RuCoverRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    Sol78Thm54Types (X ⧸ center X) → 3 ≤ CFSG.pRank 2 X

theorem ruFamilyFacts_of_coverRank (h : RuCoverRank) :
    RuFamilyFacts :=
  ruFamilyFacts_of_cover_rank h

end CFSG.EvenSporadicStandard.Induction
