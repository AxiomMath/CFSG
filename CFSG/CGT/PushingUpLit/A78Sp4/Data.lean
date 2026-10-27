module

public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.Assembly CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

@[expose] def ElemAb2 (E : Subgroup G) : Prop := ∀ x ∈ E, ∀ y ∈ E, x * y = y * x ∧ x * x = 1

@[expose] def UType (V V₂ Z Z₂ : Subgroup G) (x : G) : Prop := x ∈ V ⊓ V₂ ∧ x ∉ Z ∧ x ∉ Z₂

structure Sp4Base (G : Type) [Group G] (V V₂ J T S M M₂ : Subgroup G) (e : ℕ) : Prop where
  two_le : 2 ≤ e
  sylow : IsSylowOf 2 S ⊤
  T_le : T ≤ S
  index : T.relIndex S ≤ 2
  J_le : J ≤ T
  sup : V ⊔ V₂ = J
  elem_V : ElemAb2 V
  elem_V₂ : ElemAb2 V₂
  card_V : Nat.card V = 2 ^ (3 * e)
  card_V₂ : Nat.card V₂ = 2 ^ (3 * e)
  rank : ∀ E : Subgroup G, ElemAb2 E → Nat.card E ≤ 2 ^ (3 * e)
  A_S : ∀ E : Subgroup G, E ≤ S → ElemAb2 E → Nat.card E = 2 ^ (3 * e) → E = V ∨ E = V₂
  normal_J : (J.subgroupOf S).Normal
  card_inf : Nat.card ↥(V ⊓ V₂) = 2 ^ (2 * e)
  comm_mem : ∀ x ∈ J, ∀ y ∈ J, ⁅x, y⁆ ∈ V ⊓ V₂
  sq_mem : ∀ x ∈ J, x * x ∈ V ⊓ V₂
  inv_mem : ∀ x ∈ J, x * x = 1 → x ∈ V ∨ x ∈ V₂
  cent_S : ∀ g ∈ S, (∀ j ∈ J, ⁅g, j⁆ ∈ V ⊓ V₂) → g ∈ J
  S_inf_M : S ⊓ M = T
  S_inf_M₂ : S ⊓ M₂ = T
  T_norm : ∀ t ∈ T, cj t V = V ∧ cj t V₂ = V₂
  swap : ∀ s ∈ S, s ∉ T → cj s V = V₂ ∧ cj s V₂ = V
  exists_swap : ∃ s ∈ S, s ∉ T

structure Sp4Side (G : Type) [Group G] (L V Z J T M : Subgroup G) (e : ℕ) : Prop where
  V_le_L : V ≤ L
  L_le_M : L ≤ M
  normal_L : (L.subgroupOf M).Normal
  M_eq : M = Subgroup.normalizer (V : Set G)
  Z_eq : Z = V ⊓ Subgroup.centralizer (L : Set G)
  J_le_L : J ≤ L
  T_le_M : T ≤ M
  sylow_T : IsSylowOf 2 T M
  T_inf_L : T ⊓ L = J
  perfect : ⁅L, L⁆ = L
  cent_V : M ⊓ Subgroup.centralizer (V : Set G) ≤ V
  O2_M : ∀ P : Subgroup G, P ≤ M → IsPGroup 2 P → (P.subgroupOf M).Normal → P ≤ V
  card_Z : Nat.card Z = 2 ^ e
  cent_z : ∀ z ∈ Z, z ≠ 1 → Subgroup.centralizer ({z} : Set G) ≤ M
  normalizer_Z : Subgroup.normalizer (Z : Set G) = M
  ti : ∀ g : G, Z ⊓ cj g Z ≠ ⊥ → cj g Z = Z
  trans : ∀ z ∈ Z, z ≠ 1 → ∀ z' ∈ Z, z' ≠ 1 → ∃ m ∈ M, m * z * m⁻¹ = z'

structure Sp4Cross (G : Type) [Group G] (L L₂ V V₂ Z Z₂ J T S : Subgroup G) (e : ℕ) : Prop where
  Z_le : Z ≤ V₂
  Z₂_le : Z₂ ≤ V
  inf_Z : Z ⊓ Z₂ = ⊥
  sup_Z : Z ⊔ Z₂ = V ⊓ V₂
  T_normZ : ∀ t ∈ T, cj t Z = Z ∧ cj t Z₂ = Z₂
  swap_Z : ∀ s ∈ S, s ∉ T → cj s Z = Z₂ ∧ cj s Z₂ = Z
  conj_in_V : ∀ A : Subgroup G, (∃ g : G, A = cj g Z ∨ A = cj g Z₂) → A ≤ V →
    (A = Z ∨ A = Z₂) ∨ ((V ⊓ V₂) ⊔ A = V ∧ (V ⊓ V₂) ⊓ A = ⊥)
  conj_in_V₂ : ∀ A : Subgroup G, (∃ g : G, A = cj g Z ∨ A = cj g Z₂) → A ≤ V₂ →
    (A = Z ∨ A = Z₂) ∨ ((V ⊓ V₂) ⊔ A = V₂ ∧ (V ⊓ V₂) ⊓ A = ⊥)
  cent_L : ∀ v ∈ V ⊓ V₂, v ∉ Z → L ⊓ Subgroup.centralizer ({v} : Set G) = J
  cent_L₂ : ∀ v ∈ V ⊓ V₂, v ∉ Z₂ → L₂ ⊓ Subgroup.centralizer ({v} : Set G) = J
  inv_class : ∀ x ∈ J, x * x = 1 → x ≠ 1 → ∃ g : G,
    g⁻¹ * x * g ∈ Z ∨ g⁻¹ * x * g ∈ Z₂ ∨ UType V V₂ Z Z₂ (g⁻¹ * x * g)
  u_conj : ∀ u u' : G, UType V V₂ Z Z₂ u → UType V V₂ Z Z₂ u' →
    ∃ n ∈ Subgroup.normalizer (J : Set G), n * u * n⁻¹ = u'
  u_not_conj : ∀ u z : G, UType V V₂ Z Z₂ u → (z ∈ Z ∨ z ∈ Z₂) → z ≠ 1 →
    ∀ g : G, g⁻¹ * u * g ≠ z

structure Sp4CentL (G : Type) [Group G] (L V Z : Subgroup G) (f : G) (e : ℕ) : Prop where
  O2 : ∀ P : Subgroup G, P ≤ L ⊓ Subgroup.centralizer ({f} : Set G) → IsPGroup 2 P →
    (P.subgroupOf (L ⊓ Subgroup.centralizer ({f} : Set G))).Normal → P ≤ V
  card_CV : Nat.card ↥(V ⊓ Subgroup.centralizer ({f} : Set G)) = 2 ^ (3 * (e / 2))
  irred : ∀ X : Subgroup G, X ≤ V ⊓ Subgroup.centralizer ({f} : Set G) →
    Z ⊓ Subgroup.centralizer ({f} : Set G) ≤ X →
    (∀ k ∈ L ⊓ Subgroup.centralizer ({f} : Set G), cj k X = X) →
    X = Z ⊓ Subgroup.centralizer ({f} : Set G) ∨ X = V ⊓ Subgroup.centralizer ({f} : Set G)
  nofix : ∀ z ∈ V ⊓ Subgroup.centralizer ({f} : Set G), z ∉ Z →
    ∃ k ∈ L ⊓ Subgroup.centralizer ({f} : Set G), ⁅z, k⁆ ∉ Z

structure Sp4Field (G : Type) [Group G] (L L₂ V V₂ Z Z₂ J T S : Subgroup G) (e : ℕ) : Prop where
  S_cyclic : ∃ s ∈ S, ∀ x ∈ S, ∃ k : ℤ, (s ^ k)⁻¹ * x ∈ J
  exists_inv : T ≠ J → ∃ f ∈ T, f ∉ J ∧ f * f = 1
  even_e : T ≠ J → Even e
  inv_conj : ∀ f ∈ T, f ∉ J → f * f = 1 → ∀ x ∈ T, x ∉ J → x * x = 1 →
    ∃ j ∈ J, j⁻¹ * f * j = x
  no_inv : T ≠ J → ∀ x ∈ S, x ∉ T → x * x ≠ 1
  cent_L : ∀ f ∈ T, f ∉ J → f * f = 1 → Sp4CentL G L V Z f e
  cent_L₂ : ∀ f ∈ T, f ∉ J → f * f = 1 → Sp4CentL G L₂ V₂ Z₂ f e
  card_ZJf : ∀ f ∈ T, f ∉ J → f * f = 1 →
    Nat.card ↥((V ⊓ V₂) ⊓ Subgroup.centralizer ({f} : Set G)) = 2 ^ e

structure Sp4Coords (G : Type) [Group G] (J V V₂ Z Z₂ : Subgroup G) (F : Type) [Field F] :
    Prop where
  ex : ∃ r s t w : G → F,
    (∀ x ∈ J, ∀ y ∈ J, r (x * y) = r x + r y ∧ s (x * y) = s x + s y ∧
      t (x * y) = t x + t y + r x * s y ∧ w (x * y) = w x + w y + r x ^ 2 * s y) ∧
    (∀ x ∈ J, ∀ y ∈ J, r x = r y → s x = s y → t x = t y → w x = w y → x = y) ∧
    (∀ a b c d : F, ∃ x ∈ J, r x = a ∧ s x = b ∧ t x = c ∧ w x = d) ∧
    (∀ x ∈ J, (x ∈ V ↔ s x = 0)) ∧ (∀ x ∈ J, (x ∈ V₂ ↔ r x = 0)) ∧
    (∀ x ∈ J, (x ∈ Z ↔ r x = 0 ∧ s x = 0 ∧ t x = 0)) ∧
    (∀ x ∈ J, (x ∈ Z₂ ↔ r x = 0 ∧ s x = 0 ∧ w x = 0))

structure Sp4Loc (G : Type) [Group G] [Finite G] (L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G)
    (e : ℕ) : Prop where
  simple : IsSimpleGroup G
  charTwo : IsCharTwoType G
  base : Sp4Base G V V₂ J T S M M₂ e
  side₁ : Sp4Side G L V Z J T M e
  side₂ : Sp4Side G L₂ V₂ Z₂ J T M₂ e
  cross : Sp4Cross G L L₂ V V₂ Z Z₂ J T S e
  field : Sp4Field G L L₂ V V₂ Z Z₂ J T S e
  coords : Sp4Coords G J V V₂ Z Z₂ (GaloisField 2 e)

end CFSG.CGT.PushingUpLit.A78Sp4
