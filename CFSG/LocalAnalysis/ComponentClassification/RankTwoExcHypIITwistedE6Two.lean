module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint

@[expose] def TwistedE6TwoEvenHypII : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ →
    ChevalleyExceptionalModel (A ⧸ center A) .twistedE6 2 1 → Even (Nat.card (center A)) →
      AS76b.HypII A

end CFSG.ComponentClassification.RankTwoExcHypII
