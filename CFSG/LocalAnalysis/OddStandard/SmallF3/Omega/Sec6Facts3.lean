module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82AutFacts : Prop where
  pocket_P : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ z : G, z ∈ L → (IsI4PlusIn L z ↔ orderOf z = 2 ∧ InducesTypeSome L z 6 1 4 1)
  pocket_M : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ z : G, z ∈ L → (IsI4PlusIn L z ↔ orderOf z = 2 ∧ InducesTypeSome L z 6 (-1) 4 1)
  omega5_sub : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) →
        (∃ z ∈ layerCent L s, IsI4PlusIn L z) ∧
          ∃ u ∈ layerCent L s, orderOf u = 2 ∧ InducesTypeSome L u 6 1 2 (-1)
  aut_cent : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (X : Subgroup G),
    (IsOm6P L ∨ IsOm6M L ∨ IsOm5Q L ∨ (IsQuasisimple L ∧ IsL281 L)) → orderOf x = 2 →
    x ∈ normalizer (L : Set G) → IsComponentIn X (L ⊓ centralizer ({x} : Set G)) → InFStar X →
    (IsOm6P L → Hyp62At L) →
    ∀ R : Subgroup G, IsPGroup 2 R →
      R ≤ normalizer (L : Set G) ⊓ centralizer (X : Set G) →
        (centralizer (L : Set G)).relIndex R ≤ 2 ∨
          (IsL29 X ∧ IsOm6M L ∧
            QuotEquivTo R (R ⊓ centralizer (L : Set G))
              (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
          (IsU33 X ∧ IsOm6M L ∧
            QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4))) ∨
          (IsL29 X ∧ IsOm6P L ∧
            QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4)))
  rank_aut : ∀ (G : Type) [Group G] [Finite G] (Y E : Subgroup G), IsQuasisimple Y →
    E ≤ normalizer (Y : Set G) → CFSG.Open.IsElemAbelian 2 E →
      ((IsL29 Y ∨ IsL281 Y ∨ IsL3Eps3 Y) →
        CFSG.Open.pRank 2 E ≤ CFSG.Open.pRank 2 (E ⊓ centralizer (Y : Set G)) + 3) ∧
      (IsOmega5 Y → CFSG.Open.pRank 2 E ≤ CFSG.Open.pRank 2 (E ⊓ centralizer (Y : Set G)) + 4) ∧
      ((IsOmega6Plus Y ∨ IsOmega6Minus Y) →
        CFSG.Open.pRank 2 E ≤ CFSG.Open.pRank 2 (E ⊓ centralizer (Y : Set G)) + 5)

end CFSG.OddStandard.SmallF3.Omega
