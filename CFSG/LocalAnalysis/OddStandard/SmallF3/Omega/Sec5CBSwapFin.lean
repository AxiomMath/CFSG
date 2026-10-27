module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactI1Layer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L → ∀ r : G, orderOf r = 2 →
    (∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α) →
      IsQuasisimple (layerCent L r) ∧
        ∃ k : ↥(layerCent L r),
          orderOf (QuotientGroup.mk k : ↥(layerCent L r) ⧸ Subgroup.center ↥(layerCent L r)) = 9

@[expose] def Asc82FactI1Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L → ∀ s : G, orderOf s = 2 →
    s ∈ normalizer (L : Set G) → s ∉ centralizer (L : Set G) →
      ∀ k : ↥L, (k : G) * s = s * k →
        9 ∣ orderOf (QuotientGroup.mk k : ↥L ⧸ Subgroup.center ↥L) →
          ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α

end CFSG.OddStandard.SmallF3.Omega
