module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82Tab6M : Prop where
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
  sylow_E16 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∃ B₁ B₂ : Subgroup G, B₁ ≠ B₂ ∧ IsNormalE16In P B₁ ∧
      IsNormalE16In P B₂ ∧ ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 → B = B₁ ∨ B = B₂
  aut_B : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 →
      Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) ∧
        (∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ n ∈ L ⊓ normalizer (B : Set G), n * b * n⁻¹ = b') ∧
        L ⊓ centralizer (B : Set G) = B ⊔ centerIn L
  cent_B : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 →
      ∀ x : G, x ∈ normalizer (L : Set G) → (∀ b ∈ B, x * b = b * x) →
        (∃ b ∈ B, x * b⁻¹ ∈ centralizer (L : Set G)) ∨
          (∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 1 α) ∨ ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 3 α
  outer_swaps : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → InducesOutsideGStar L 6 (-1) s →
      ∀ U : Subgroup G, U ≤ L → IsElemAb2 U 4 → s ∉ normalizer (U : Set G)
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
  xout_eq : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → layerCent L s ≠ ⊥ →
      XOut L s = layerCent L s
  xout_i3 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) →
        XOut L s = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G)))

end CFSG.OddStandard.SmallF3.Omega
