module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.RankTwoStandard

@[expose] def ExcEvenMultiplier : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ →
    RankTwoExceptionalEvenType (A ⧸ center A) → Even (Nat.card (center A)) →
      ChevalleyExceptionalModel (A ⧸ center A) .G2 2 2 ∨
        ChevalleyExceptionalModel (A ⧸ center A) .F4 2 1 ∨
        ChevalleyExceptionalModel (A ⧸ center A) .twistedE6 2 1

end CFSG.ComponentClassification.RankTwoExcHypII
