module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTab6PClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PField1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PField2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PField3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PField4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PField5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PTab7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Tab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure FFTab6P2Local : Prop where
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

theorem ffCls_of (h : FFTab6PClass) : FF6PCls :=
  ⟨h.center_triv, h.nontrivial, h.excl, h.layer_i1, h.xout_eq⟩

theorem ffTab6P2Local_holds (h : FFTab6PClass) : FFTab6P2Local where
  sylow_E16 := ff6p_sylow_E16
  aut_B := ff6p_aut_B (ffCls_of h)
  cent_B := ff6p_cent_B (ffCls_of h)
  cent_B_opp := ff6p_cent_B_opp (ffCls_of h)
  cent_B_index := ff6p_cent_B_index (ffCls_of h)
  center_le := ff6p_center_le
  i1_cent := ff6p_i1_cent (ffCls_of h)
  cent_B_sylow := ff6p_cent_B_sylow (ffCls_of h)
  aut_cent_i1 := ff6p_aut_cent_i1 (ffCls_of h)
  no_normal_z4 := ff6p_no_normal_z4 (ffCls_of h)

theorem asc82Tab6P_of (h₁ : FFTab6PClass) (h₂ : FFTab6P2Local) : Asc82Tab6P where
  layer_trivial := h₁.layer_trivial
  layer_i1 := h₁.layer_i1
  layer_i2 := h₁.layer_i2
  layer_outer := h₁.layer_outer
  inner_iff := h₁.inner_iff
  out_two := h₁.out_two
  i4_one_class := h₁.i4_one_class
  i2_one_class := h₁.i2_one_class
  cover_i4 := h₁.cover_i4
  inv_of_i4m := h₁.inv_of_i4m
  i4m_of_inv := h₁.i4m_of_inv
  sylow_E16 := h₂.sylow_E16
  aut_B := h₂.aut_B
  cent_B := h₂.cent_B
  cent_B_opp := h₂.cent_B_opp
  classify := h₁.classify
  nontrivial := h₁.nontrivial
  layer_om5_iff := h₁.layer_om5_iff
  prod_i2 := h₁.prod_i2
  excl := h₁.excl
  center_triv := h₁.center_triv
  xout_eq := h₁.xout_eq
  xout_i3 := h₁.xout_i3
  cent_B_index := h₂.cent_B_index
  center_le := h₂.center_le
  i1_cent := h₂.i1_cent
  cent_B_sylow := h₂.cent_B_sylow
  aut_cent_i1 := h₂.aut_cent_i1
  no_normal_z4 := h₂.no_normal_z4

theorem asc82Tab6P_holds (hGA : CFSG.Open.GriessAllModelsStatement) : Asc82Tab6P :=
  asc82Tab6P_of (ffTab6PClass_holds hGA) (ffTab6P2Local_holds (ffTab6PClass_holds hGA))

theorem asc82Tab7P_of (h : FFTab6PClass)
    (hpocket : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
      ∀ z : G, z ∈ L → (IsI4PlusIn L z ↔ orderOf z = 2 ∧ InducesTypeSome L z 6 1 4 1)) :
    Asc82Tab7P where
  hyp62_of_sylow := ff6p_hyp62_of_sylow (ffCls_of h)
  aut_B_types := ff6p_aut_B_types (ffCls_of h) hpocket

theorem asc82Tab7P_holds (hGA : CFSG.Open.GriessAllModelsStatement)
    (hpocket : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
      ∀ z : G, z ∈ L → (IsI4PlusIn L z ↔ orderOf z = 2 ∧ InducesTypeSome L z 6 1 4 1)) :
    Asc82Tab7P :=
  asc82Tab7P_of (ffTab6PClass_holds hGA) hpocket

end CFSG.OddStandard.SmallF3.Omega
