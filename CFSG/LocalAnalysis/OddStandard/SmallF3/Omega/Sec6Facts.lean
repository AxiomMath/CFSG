module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def KindP (L : Subgroup G) (s : G) : ℕ → Prop
  | 0 => InducesTypeSome L s 6 1 4 1
  | 1 => InducesTypeSome L s 6 1 2 (-1)
  | 2 => ∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α
  | 3 => ∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α
  | _ => InducesOutsideGStar L 6 1 s

structure Asc82Tab6P : Prop where
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
  sylow_E16 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∃ B₁ B₂ : Subgroup G, B₁ ≠ B₂ ∧ IsNormalE16In P B₁ ∧
      IsNormalE16In P B₂ ∧ ∀ B : Subgroup G, IsNormalE16In P B → B = B₁ ∨ B = B₂
  aut_B : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B →
      QuotEquivTo (L ⊓ normalizer (B : Set G)) B (Equiv.Perm (Fin 5)) ∧
        L ⊓ centralizer (B : Set G) = B ∧
        ∃ φ : (Fin 5 → ZMod 2) → G,
          IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤
  cent_B : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B →
      ∀ x : G, x ∈ normalizer (L : Set G) → (∀ b ∈ B, x * b = b * x) →
        (∃ b ∈ B, x * b⁻¹ ∈ centralizer (L : Set G)) ∨
          ∃ b ∈ B, (∃ α : ℤˣ, InducesTypeSome L (x * b⁻¹) 6 1 1 α) ∧
            ∀ n ∈ L ⊓ normalizer (B : Set G), (x * b⁻¹) * n = n * (x * b⁻¹)
  cent_B_opp : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B B' : Subgroup G, IsNormalE16In P B →
      IsNormalE16In P B' → B ≠ B' → ∀ z : G, z ∈ centerIn P → IsI4PlusIn L z →
        ∀ x : G, x ∈ normalizer (L : Set G) → (∀ b ∈ B, x * b = b * x) →
          (∀ n ∈ L ⊓ normalizer (B : Set G), x * n = n * x) →
          (∃ α : ℤˣ, InducesTypeSome L x 6 1 1 α) →
            (∀ n ∈ L ⊓ normalizer (B' : Set G), (x * z) * n = n * (x * z)) ∧
              ∃ α : ℤˣ, TypesInModel L 6 1 1 α 1 (-α) x (x * z)
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
  cent_B_index : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B →
      ∀ x y : G, x ∈ normalizer (L : Set G) → y ∈ normalizer (L : Set G) →
        (∀ b ∈ B, x * b = b * x) → (∀ b ∈ B, y * b = b * y) →
        (∀ b ∈ B, x * b⁻¹ ∉ centralizer (L : Set G)) →
        (∀ b ∈ B, y * b⁻¹ ∉ centralizer (L : Set G)) →
          ∃ b ∈ B, x * y⁻¹ * b⁻¹ ∈ centralizer (L : Set G)
  center_le : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B → centerIn P ≤ B
  i1_cent : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L →
    ∀ y : G, orderOf y = 2 → y ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L y 6 1 1 α) →
        ∃ l ∈ L, ∃ B : Subgroup G, IsNormalE16In P B ∧
          ∀ n ∈ L ⊓ normalizer (B : Set G), (l⁻¹ * y * l) * n = n * (l⁻¹ * y * l)
  cent_B_sylow : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ H S₁ : Subgroup G, L ≤ H → H ≤ normalizer (L : Set G) → IsSylow2Of S₁ H →
      ∀ B : Subgroup G, IsNormalE16In (S₁ ⊓ L) B →
        ∀ x ∈ H, (∀ b ∈ B, x * b = b * x) → ∃ s ∈ S₁, s⁻¹ * x ∈ centralizer (L : Set G)
  aut_cent_i1 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) →
        ∀ R : Subgroup G,
          R ≤ normalizer (L : Set G) ⊓ centralizer ((layerCent L s : Subgroup G) : Set G) →
          (centralizer (L : Set G)).relIndex R ≤ 2
  no_normal_z4 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ H S₁ : Subgroup G, L ≤ H → H ≤ normalizer (L : Set G) → IsSylow2Of S₁ H →
      ∀ w ∈ S₁, w ^ 4 ∈ centralizer (L : Set G) → w ^ 2 ∉ centralizer (L : Set G) →
        (∀ y ∈ S₁, y⁻¹ * w * y ∈ zpowers w ⊔ centralizer (L : Set G)) → False

end CFSG.OddStandard.SmallF3.Omega
