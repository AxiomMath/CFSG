module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTab6PF1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTab6PF2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTab6PF3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure FFTab6PClass : Prop where
  layer_trivial : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (layerCent L s = ⊥ ↔
        InducesTypeSome L s 6 1 4 1 ∨ ∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α)
  layer_i1 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) → IsOmega5 (layerCent L s)
  layer_i2 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesTypeSome L s 6 1 2 (-1) → IsL29 (layerCent L s)
  layer_outer : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesOutsideGStar L 6 1 s → IsL3Eps3 (layerCent L s) ∨ IsL29 (layerCent L s)
  inner_iff : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ((InnerOn L s ∧ s ∉ centralizer (L : Set G)) ↔
        InducesTypeSome L s 6 1 4 1 ∨ InducesTypeSome L s 6 1 2 (-1))
  out_two : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ x : G, x ∈ normalizer (L : Set G) → Odd (orderOf x) → InnerOn L x
  i4_one_class : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ u u' : G, u ∈ L → u' ∈ L → orderOf u = 2 → orderOf u' = 2 →
      InducesTypeSome L u 6 1 4 1 → InducesTypeSome L u' 6 1 4 1 → u' ∈ conjClassIn L u
  i2_one_class : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ u u' : G, u ∈ L → u' ∈ L → orderOf u = 2 → orderOf u' = 2 →
      InducesTypeSome L u 6 1 2 (-1) → InducesTypeSome L u' 6 1 2 (-1) → u' ∈ conjClassIn L u
  cover_i4 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ((∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) ∨ InducesOutsideGStar L 6 1 s) →
        ∃ u ∈ XOut L s, orderOf u = 2 ∧ InducesTypeSome L u 6 1 4 1 ∧ s * u ∈ conjClassIn L s
  inv_of_i4m : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → InducesTypeSome L s 6 1 2 (-1) →
      ∀ u ∈ XOut L s, orderOf u = 2 → InducesTypeSome L u 6 1 2 (-1)
  i4m_of_inv : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → IsL29 (XOut L s) →
      (∀ u ∈ XOut L s, orderOf u = 2 → InducesTypeSome L u 6 1 2 (-1)) →
        InducesTypeSome L s 6 1 2 (-1)
  classify : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      s ∈ centralizer (L : Set G) ∨ InducesTypeSome L s 6 1 4 1 ∨ InducesTypeSome L s 6 1 2 (-1) ∨
        (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) ∨ (∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) ∨
        InducesOutsideGStar L 6 1 s
  nontrivial : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (InducesTypeSome L s 6 1 4 1 ∨ InducesTypeSome L s 6 1 2 (-1) ∨
        (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) ∨ (∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) ∨
        InducesOutsideGStar L 6 1 s) → s ∉ centralizer (L : Set G)
  layer_om5_iff : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (IsOmega5 (layerCent L s) ↔ ∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α)
  prod_i2 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ v : G, v ∈ L → InducesTypeSome L v 6 1 2 (-1) → ∀ u ∈ XOut L v, orderOf u = 2 →
      orderOf (u * v) = 2 ∧ InducesTypeSome L (u * v) 6 1 4 1
  excl : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → KindP L s i → ¬ KindP L s j
  center_triv : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L → centerIn L = ⊥
  xout_eq : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → layerCent L s ≠ ⊥ →
      XOut L s = layerCent L s
  xout_i3 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) →
      XOut L s = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G)))

theorem ffTab6PClass_holds (hGA : CFSG.Open.GriessAllModelsStatement) : FFTab6PClass where
  layer_trivial := ff_layer_trivial hGA
  layer_i1 := ff_layer_i1 hGA
  layer_i2 := ff_layer_i2 hGA
  layer_outer := ff_layer_outer hGA
  inner_iff := ff_inner_iff hGA
  out_two := ff_out_two_six_plus
  i4_one_class := ff_i4_one_class hGA
  i2_one_class := ff_i2_one_class hGA
  cover_i4 := ff_cover_i4 hGA
  inv_of_i4m := ff_inv_of_i4m hGA
  i4m_of_inv := ff_i4m_of_inv hGA
  classify := ff_classify hGA
  nontrivial := ff_nontrivial hGA
  layer_om5_iff := ff_layer_om5_iff hGA
  prod_i2 := ff_prod_i2 hGA
  excl := ff_excl hGA
  center_triv := fun _ _ _ L hL => ff_centerIn_eq_bot_six_plus hGA hL
  xout_eq := ff_xout_eq hGA
  xout_i3 := ff_xout_i3 hGA

end CFSG.OddStandard.SmallF3.Omega
