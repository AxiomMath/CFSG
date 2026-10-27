module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup

@[expose] def Step16NotFourPoints : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Frame G A A R g E F → Even (Nat.card (center A)) → Nat.card (pointsIn R (E ⊓ F)) ≠ 4

end CFSG.ComponentClassification.AS81
