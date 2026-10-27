module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup

variable {G : Type} [Group G]

structure L4Actual (S : Subgroup G) (z t : G) (a : ℕ) (Z X : Set G) (US : Subgroup G) : Prop where
  z_Z : z ∈ Z
  t_Z : t ∈ Z
  tz_X : t * z ∈ X
  partition : ∀ y ∈ S, y * y = 1 → y ≠ 1 → (y ∈ Z ∨ y ∈ X) ∧ ¬ (y ∈ Z ∧ y ∈ X)
  card_Ct : Nat.card ↥(S ⊓ centralizer ({t} : Set G)) = 2 ^ (a + 2)
  US_le : US ≤ S ⊓ centralizer ({t} : Set G)
  US_normal : ∀ c ∈ S ⊓ centralizer ({t} : Set G), ∀ d ∈ US, c * d * c⁻¹ ∈ US
  US_card : Nat.card ↥US = 2 ^ (a - 1)
  US_dih : IVK.IsDihedralTwoGroup ↥US (a - 1)
  US_inter : ∀ y ∈ US, y ∈ zpowers z ⊔ zpowers t → y = 1
  US_cls : ∀ d ∈ US, d * d = 1 → d ≠ 1 → d ∈ X ∧ z * d ∈ X ∧ t * d ∈ X ∧ t * z * d ∈ Z

structure L4Decomp (T D₁ D₂ T₁ U : Subgroup G) (z u w0 : G) (a : ℕ) (Z X : Set G) : Prop where
  D₁_dih : IVK.IsDihedralTwoGroup ↥D₁ a
  D₂_dih : IVK.IsDihedralTwoGroup ↥D₂ a
  D₁_le : D₁ ≤ T
  D₂_le : D₂ ≤ T
  comm : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x
  inter : D₁ ⊓ D₂ = ⊥
  T_le : T ≤ D₁ ⊔ D₂
  u_mem : u ∈ D₁
  center_D₁ : (center ↥D₁).map D₁.subtype = zpowers u
  w0_mem : w0 ∈ D₁
  uz_mem : u * z ∈ D₂
  U_le : U ≤ D₂
  D₂_card : Nat.card ↥D₂ = 2 * Nat.card ↥U
  uz_U : u * z ∈ U
  T₁_le : T₁ ≤ D₁
  T₁_cyc : IsCyclic ↥T₁
  u_T₁ : u ∈ T₁
  T₁_idx : T₁.relIndex D₁ = 2
  T₁_refl : ∀ d ∈ D₁, d ∉ T₁ → d * d = 1
  sep : ∀ s ∈ D₁, s ∉ T₁ → ∀ m ∈ T₁ ⊔ D₂, m * m = 1 → m ≠ 1 → m ≠ u →
    ¬ ((s ∈ Z ↔ m ∈ Z) ∧ (u * s ∈ Z ↔ u * m ∈ Z))
  D₂_cls : ∀ d ∈ D₂, d * d = 1 → d ≠ 1 → d ∈ X ∧ u * d ∈ Z
  derived : ∀ y ∈ ⁅T, T⁆, y * y = 1 → y ∈ zpowers z ⊔ zpowers u
  u_derived : u ∈ ⁅D₁, D₁⁆

structure L4Std (S : Subgroup G) (z u : G) (a : ℕ) (Z X : Set G) : Prop where
  u_X : u ∈ X
  uz_X : u * z ∈ X
  index : (S ⊓ centralizer ({u} : Set G)).relIndex S = 2
  center : (center ↥(S ⊓ centralizer ({u} : Set G))).map (S ⊓ centralizer ({u} : Set G)).subtype =
    zpowers z ⊔ zpowers u
  decomp : ∀ w0 : G, w0 ∈ S ⊓ centralizer ({u} : Set G) → w0 * w0 = 1 → w0 ∈ Z → w0 ≠ z → u * w0 ∈ Z →
    Nat.card ↥(S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G)) = 2 ^ (a + 2) →
    ∀ U : Subgroup G, U ≤ S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G) →
      (∀ c ∈ S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G), ∀ d ∈ U, c * d * c⁻¹ ∈ U) →
      Nat.card ↥U = 2 ^ (a - 1) → IVK.IsDihedralTwoGroup ↥U (a - 1) →
      (∀ y ∈ U, y ∈ zpowers u ⊔ zpowers w0 → y = 1) →
      (∀ d ∈ U, d * d = 1 → d ≠ 1 → d ∈ X ∧ w0 * d ∈ X ∧ u * w0 * d ∈ X ∧ u * d ∈ Z) →
      ∃ D₁ D₂ T₁ : Subgroup G, L4Decomp (S ⊓ centralizer ({u} : Set G)) D₁ D₂ T₁ U z u w0 a Z X

end CFSG.GH74.GLS.Stage2.Local.P27
