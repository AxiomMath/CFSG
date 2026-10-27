module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Kind5 (L : Subgroup G) (s : G) : ℕ → Prop
  | 0 => InnerOn L s ∧ s ∉ centralizer (L : Set G)
  | 1 => InducesTypeSome L s 6 (-1) 4 (-1)
  | 2 => ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α
  | 3 => ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α
  | 4 => InducesProjective L 6 (-1) s
  | _ => InducesOutsideGStar L 6 (-1) s

structure Asc82Tab5 : Prop where
  classify : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      s ∈ centralizer (L : Set G) ∨ Kind5 L s 0 ∨ Kind5 L s 1 ∨ Kind5 L s 2 ∨ Kind5 L s 3 ∨
        Kind5 L s 4 ∨ Kind5 L s 5
  excl : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → Kind5 L s i → ¬ Kind5 L s j
  kind_ne_central : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (Kind5 L s 1 ∨ Kind5 L s 2 ∨ Kind5 L s 3 ∨ Kind5 L s 4 ∨ Kind5 L s 5) →
        s ∉ centralizer (L : Set G)
  layer_trivial : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      layerCent L s = ⊥ → Kind5 L s 0 ∨ Kind5 L s 3
  pocket_kind : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ z : G, IsI4PlusIn L z → Kind5 L z 0
  inner_lift : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 0 →
      ∃ w ∈ L, orderOf w = 2 ∧ w⁻¹ * s ∈ centralizer (L : Set G)
  inv_classes : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, t ∈ centerIn L → orderOf t = 2 → ∀ z : G, IsI4PlusIn L z →
      ∀ u ∈ L, orderOf u = 2 → u ≠ t → u ∈ conjClassIn L z ∨ u ∈ conjClassIn L (t * z)
  tz_not_pocket : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, t ∈ centerIn L → orderOf t = 2 → ∀ z : G, IsI4PlusIn L z → ¬ IsI4PlusIn L (t * z)
  f53 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ t : G, t ∈ centerIn L → orderOf t = 2 →
      ∀ z : G, IsI4PlusIn L z → z ∈ centerIn P →
        centerIn P = zpowers t ⊔ zpowers z ∧
          ∀ x : G, x ∈ normalizer (L : Set G) → (∀ p ∈ P, x * p = p * x) →
            ∃ c ∈ centralizer (L : Set G), ∃ w ∈ centerIn P, x = w * c
  xout_eq : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → layerCent L s ≠ ⊥ →
      XOut L s = layerCent L s
  xout_i3 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 3 →
      XOut L s = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G)))
  cover_i4 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (Kind5 L s 3 ∨ Kind5 L s 4 ∨ Kind5 L s 5) →
        ∃ u ∈ XOut L s, orderOf u = 2 ∧ IsI4PlusIn L u ∧ s * u ∈ conjClassIn L s
  layer_i4m : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 1 →
      IsComponentIn (layerCent L s) (L ⊓ centralizer ({s} : Set G)) ∧ IsL29 (layerCent L s)
  i4m_inv : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 1 →
      ∀ u ∈ layerCent L s, orderOf u = 2 → ¬ IsI4PlusIn L u ∧ u ∉ centerIn L
  i4m_of_comp : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ∀ J : Subgroup G, IsComponentIn J (L ⊓ centralizer ({s} : Set G)) → IsL29 J →
        (∀ u ∈ J, orderOf u = 2 → ¬ IsI4PlusIn L u) → Kind5 L s 1
  prod_i4m : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 1 →
      ∀ u ∈ layerCent L s, orderOf u = 2 → Kind5 L (s * u) 1

end CFSG.OddStandard.SmallF3.Omega
