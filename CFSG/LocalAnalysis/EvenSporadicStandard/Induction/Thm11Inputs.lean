module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitStd

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def Sol78Thm11SuzONan : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.oddCore G = ⊥ → ∀ A : Subgroup G, SolStd A →
    Odd (Nat.card ↥(center ↥A)) →
      (IsSporadic (↥A ⧸ center ↥A) .Suz ∨ IsSporadic (↥A ⧸ center ↥A) .ONan) → EmbedsInPair A

end CFSG.EvenSporadicStandard.Induction
