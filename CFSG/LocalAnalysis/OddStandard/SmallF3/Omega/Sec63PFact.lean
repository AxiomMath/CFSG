module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactOm6PA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G) (x : G) (V : Subgroup G), IsOm6P Y →
    orderOf x = 2 → x ∈ normalizer (Y : Set G) → x ∉ centralizer (Y : Set G) →
    IsComponentIn V (Y ⊓ centralizer ({x} : Set G)) → IsL29 V →
    ∀ b ∈ V, orderOf b = 2 →
      IsI4PlusIn Y b ∨
      ∃ Vb : Subgroup G, IsComponentIn Vb (Y ⊓ centralizer ({b} : Set G)) ∧ IsL29 Vb ∧
        InFStar Vb ∧
        (∀ K : Subgroup G, IsComponentIn K (Y ⊓ centralizer ({b} : Set G)) → K = Vb) ∧
        (∀ P : Subgroup G, IsPGroup 2 P →
          P ≤ V ⊓ centralizer ({b} : Set G) ⊓ centralizer (Vb : Set G) → Nat.card P ≤ 2) ∧
        ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ V ⊓ centralizer ({b} : Set G) ∧ Nat.card R = 8 ∧
          R = closure {r : G | r ∈ R ∧ orderOf r = 2}

end CFSG.OddStandard.SmallF3.Omega
