module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MField1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MField2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure FF6MClass : Prop where
  layer_trivial : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (layerCent L s = ⊥ ↔
        InducesTypeSome L s 6 (-1) 4 1 ∨ ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α)
  layer_i4m : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesTypeSome L s 6 (-1) 4 (-1) → IsL29 (layerCent L s)
  layer_rho : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesProjective L 6 (-1) s → IsU33 (layerCent L s)
  layer_i1 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α) → IsOmega5 (layerCent L s)
  layer_gamma : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesOutsideGStar L 6 (-1) s → IsL29 (layerCent L s)
  inner_iff : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ((InnerOn L s ∧ s ∉ centralizer (L : Set G)) ↔ InducesTypeSome L s 6 (-1) 4 1)
  out_two : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ x : G, x ∈ normalizer (L : Set G) → Odd (orderOf x) → InnerOn L x
  inv_one_class : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ u u' : G, u ∈ L → u' ∈ L → orderOf u = 2 → orderOf u' = 2 → u' ∈ conjClassIn L u
  ex_u_outer : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → ¬ InnerOn L s →
      ∃ u ∈ twoRes (L ⊓ centralizer ({s} : Set G)), orderOf u = 2 ∧ s * u ∈ conjClassIn L s
  xout_eq : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → layerCent L s ≠ ⊥ →
      XOut L s = layerCent L s
  xout_i3 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) →
        XOut L s = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G)))
  classify : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      s ∈ centralizer (L : Set G) ∨ InducesTypeSome L s 6 (-1) 4 1 ∨
        InducesTypeSome L s 6 (-1) 4 (-1) ∨ InducesProjective L 6 (-1) s ∨
        (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α) ∨ (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) ∨
        InducesOutsideGStar L 6 (-1) s
  nontrivial : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (InducesTypeSome L s 6 (-1) 4 1 ∨ InducesTypeSome L s 6 (-1) 4 (-1) ∨
        InducesProjective L 6 (-1) s ∨ (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α) ∨
        (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) ∨ InducesOutsideGStar L 6 (-1) s) →
        s ∉ centralizer (L : Set G)

theorem ffTab6MClass_holds : FF6MClass where
  layer_trivial := ff6m_layer_trivial
  layer_i4m := ff6m_layer_i4m
  layer_rho := ff6m_layer_rho
  layer_i1 := ff6m_layer_i1
  layer_gamma := ff6m_layer_gamma
  inner_iff := ff6m_inner_iff
  out_two := ff_out_two_six_minus
  inv_one_class := ff6m_inv_one_class
  ex_u_outer := ff6m_ex_u_outer
  xout_eq := ff6m_xout_eq
  xout_i3 := ff6m_xout_i3
  classify := ff6m_classify
  nontrivial := ff6m_nontrivial

end CFSG.OddStandard.SmallF3.Omega
