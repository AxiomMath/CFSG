module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactOuterI4m : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ P : Subgroup G, IsSylow2Of P L →
      ∀ s0 ∈ normalizer (L : Set G) ⊓ normalizer (JElem P : Set G),
        orderOf s0 = 2 → s0 ∉ L ⊔ centralizer (L : Set G) →
          ∃ b ∈ JElem P, s0 * b = b * s0 ∧
            IsComponentIn (layerCent L (s0 * b)) (L ⊓ centralizer ({s0 * b} : Set G)) ∧
            IsL29 (layerCent L (s0 * b))

end CFSG.OddStandard.SmallF3.Omega
