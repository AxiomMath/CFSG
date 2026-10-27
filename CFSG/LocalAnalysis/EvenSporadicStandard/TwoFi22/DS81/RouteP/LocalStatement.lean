module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Out

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def Fi24RecognitionLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → Nat.card (center L) = 2 →
    IsSporadic (L ⧸ center L) .Fi22 → ∀ {t : G}, (center L).map L.subtype = zpowers t →
    L.relIndex (centralizer ({t} : Set G)) = 2 →
    ∀ E : Subgroup G, E ≤ L → M24Out G E t → IsSporadic G .Fi24Prime

end CFSG.EvenSporadicStandard.TwoFi22.DS81
