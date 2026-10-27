module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactInvB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ P : Subgroup G, IsSylow2Of P L →
      ∀ u ∈ L, u * u = 1 → ∃ l ∈ L, ∃ b ∈ JElem P, l⁻¹ * u * l = b

end CFSG.OddStandard.SmallF3.Omega
