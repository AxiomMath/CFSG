module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Hyp

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

variable {G : Type} [Group G] {L : Subgroup G} {t u : G}

@[expose] def Sol78CenterInv (L : Subgroup G) : Prop :=
  ∀ a ∈ L, orderOf a = 2 → ∀ z ∈ L, z * z = 1 → z * a = a * z →
    (∀ y ∈ L, y * a = a * y → z * y = y * z) → z = 1 ∨ z = a

end CFSG.EvenSporadicStandard.Solomon78
