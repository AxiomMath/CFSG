module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLocal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def RuQ (H : Type) [Group H] (L K : Subgroup H) (u : H) : Prop :=
  RuPair H L K u ∧ (∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2) ∧
    ∀ [Finite H] (N : Subgroup H) (t : H), SolomonHypQ H N L K t u → t ∈ N

end CFSG.EvenSporadicStandard.Induction
