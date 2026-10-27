module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82RankOm6M : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G), IsOm6M L → U ≤ L →
    CFSG.Open.IsElemAbelian 2 U → Nat.card U ≤ 16

@[expose] def Asc82E16Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L F : Subgroup G), IsOm6M L →
    F ≤ normalizer (L : Set G) → IsElemAb2 F 4 → F ⊓ centralizer (L : Set G) = ⊥ →
      (∀ f ∈ F, orderOf f = 2 → layerCent L f = ⊥) → ∀ f ∈ F, InnerOn L f

end CFSG.OddStandard.SmallF3.Omega
