module

public import CFSG.CGT.PushingUpLit.A78Sp4.Data

public section

namespace CFSG.CGT.PushingUpLit.A78T2

open CFSG.Assembly CFSG.ABGLocalTools
open CFSG.CGT.PushingUpLit.A78Sp4 (cj ElemAb2)
open scoped commutatorElement

structure T2Base (G : Type) [Group G] (V V₂ Z J T S M M₂ : Subgroup G) (e : ℕ) : Prop where
  two_le : 2 ≤ e
  sylow : IsSylowOf 2 S ⊤
  T_le : T ≤ S
  index : T.relIndex S ≤ 2
  exists_swap : ∃ s ∈ S, s ∉ T
  J_le : J ≤ T
  sup : V ⊔ V₂ = J
  inf : V ⊓ V₂ = Z
  elem_V : ElemAb2 V
  elem_V₂ : ElemAb2 V₂
  card_V : Nat.card V = 2 ^ (2 * e)
  card_V₂ : Nat.card V₂ = 2 ^ (2 * e)
  card_Z : Nat.card Z = 2 ^ e
  rank : ∀ E : Subgroup G, ElemAb2 E → Nat.card E ≤ 2 ^ (2 * e)
  A_S : ∀ E : Subgroup G, E ≤ S → ElemAb2 E → Nat.card E = 2 ^ (2 * e) → E = V ∨ E = V₂
  normal_J : (J.subgroupOf S).Normal
  comm_mem : ∀ x ∈ J, ∀ y ∈ J, ⁅x, y⁆ ∈ Z
  sq_mem : ∀ x ∈ J, x * x ∈ Z
  inv_mem : ∀ x ∈ J, x * x = 1 → x ∈ V ∨ x ∈ V₂
  cent_S : ∀ g ∈ S, (∀ j ∈ J, ⁅g, j⁆ ∈ Z) → g ∈ J
  S_inf_M : S ⊓ M = T
  S_inf_M₂ : S ⊓ M₂ = T
  index_J : J.relIndex S ≤ 2 * e
  T_norm : ∀ t ∈ T, cj t V = V ∧ cj t V₂ = V₂
  swap : ∀ s ∈ S, s ∉ T → cj s V = V₂ ∧ cj s V₂ = V

structure T2Side (G : Type) [Group G] (L V Z J T M : Subgroup G) (e : ℕ) : Prop where
  V_le_L : V ≤ L
  L_le_M : L ≤ M
  normal_L : (L.subgroupOf M).Normal
  M_eq : M = Subgroup.normalizer (V : Set G)
  J_le_L : J ≤ L
  T_le_M : T ≤ M
  sylow_T : IsSylowOf 2 T M
  T_inf_L : T ⊓ L = J
  trans : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ l ∈ L, l * v * l⁻¹ = w
  cent_L : ∀ z ∈ Z, z ≠ 1 → L ⊓ Subgroup.centralizer ({z} : Set G) = J

structure T2Heis (G : Type) [Group G] (J V V₂ Z : Subgroup G) (F : Type) [Field F]
    (a b c : G → F) : Prop where
  add_a : ∀ x ∈ J, ∀ y ∈ J, a (x * y) = a x + a y
  add_b : ∀ x ∈ J, ∀ y ∈ J, b (x * y) = b x + b y
  ker_a : ∀ x ∈ J, (x ∈ V₂ ↔ a x = 0)
  ker_b : ∀ x ∈ J, (x ∈ V ↔ b x = 0)
  surj_ab : ∀ p q : F, ∃ x ∈ J, a x = p ∧ b x = q
  add_c : ∀ x ∈ Z, ∀ y ∈ Z, c (x * y) = c x + c y
  inj_c : ∀ x ∈ Z, ∀ y ∈ Z, c x = c y → x = y
  surj_c : ∀ r : F, ∃ x ∈ Z, c x = r
  comm : ∀ x ∈ J, ∀ y ∈ J, c ⁅x, y⁆ = a x * b y + a y * b x

structure T2Tori (G : Type) [Group G] (J Z L L₂ : Subgroup G) (F : Type) [Field F]
    (a b c : G → F) : Prop where
  torus₁ : ∀ t : F, t ≠ 0 → ∃ x ∈ L, (∀ j ∈ J, x * j * x⁻¹ ∈ J) ∧
    (∀ j ∈ J, a (x * j * x⁻¹) = t⁻¹ * a j ∧ b (x * j * x⁻¹) = t ^ 2 * b j) ∧
    ∀ z ∈ Z, x * z * x⁻¹ ∈ Z ∧ c (x * z * x⁻¹) = t * c z
  torus₂ : ∀ t : F, t ≠ 0 → ∃ x ∈ L₂, (∀ j ∈ J, x * j * x⁻¹ ∈ J) ∧
    (∀ j ∈ J, a (x * j * x⁻¹) = t ^ 2 * a j ∧ b (x * j * x⁻¹) = t⁻¹ * b j) ∧
    ∀ z ∈ Z, x * z * x⁻¹ ∈ Z ∧ c (x * z * x⁻¹) = t * c z

structure T2CentL (G : Type) [Group G] (L V Z : Subgroup G) (f : G) (e : ℕ) : Prop where
  O2 : ∀ P : Subgroup G, P ≤ L ⊓ Subgroup.centralizer ({f} : Set G) → IsPGroup 2 P →
    (P.subgroupOf (L ⊓ Subgroup.centralizer ({f} : Set G))).Normal → P ≤ V
  card_CV : 2 ^ e ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({f} : Set G))
  irred : ∀ X : Subgroup G, X ≤ V ⊓ Subgroup.centralizer ({f} : Set G) →
    (∀ k ∈ L ⊓ Subgroup.centralizer ({f} : Set G), cj k X = X) →
    X = ⊥ ∨ X = V ⊓ Subgroup.centralizer ({f} : Set G)
  card_CZ : Nat.card ↥(Z ⊓ Subgroup.centralizer ({f} : Set G)) < 2 ^ e

structure T2Field (G : Type) [Group G] (L L₂ V V₂ Z J T S : Subgroup G) (e : ℕ) : Prop where
  fixZ : ∀ x ∈ T, x ∉ J → (∃ v ∈ V, ⁅x, v⁆ ∉ Z) ∧ (∃ v ∈ V₂, ⁅x, v⁆ ∉ Z)
  card_CJ : ∀ a ∈ S, a ∉ J → a * a = 1 →
    2 ^ e ≤ Nat.card ↥(J ⊓ Subgroup.centralizer ({a} : Set G))
  exists_inv : T ≠ J → ∃ f ∈ T, f ∉ J ∧ f * f = 1
  even_e : T ≠ J → Even e
  inv_conj : ∀ f ∈ T, f ∉ J → f * f = 1 → ∀ x ∈ T, x ∉ J → x * x = 1 →
    ∃ j ∈ J, j⁻¹ * f * j = x
  card_CJf : ∀ f ∈ T, f ∉ J → f * f = 1 →
    2 ^ (e + e / 2) ≤ Nat.card ↥(J ⊓ Subgroup.centralizer ({f} : Set G))
  cent_L : ∀ f ∈ T, f ∉ J → f * f = 1 → T2CentL G L V Z f e
  cent_L₂ : ∀ f ∈ T, f ∉ J → f * f = 1 → T2CentL G L₂ V₂ Z f e
  types : ∀ a ∈ S, a ∉ T → a * a = 1 →
    J ⊓ Subgroup.centralizer ({a} : Set G) = Z ∨
      ((∀ x ∈ J ⊓ Subgroup.centralizer ({a} : Set G), x * x = 1 → x ∈ Z) ∧
        Nat.card ↥(Z ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 2 ^ (e / 2))

structure T2Loc (G : Type) [Group G] [Finite G] (L L₂ V V₂ Z J T S M M₂ : Subgroup G) (e : ℕ) :
    Prop where
  three_le : 3 ≤ e
  simple : IsSimpleGroup G
  charTwo : IsCharTwoType G
  base : T2Base G V V₂ Z J T S M M₂ e
  side₁ : T2Side G L V Z J T M e
  side₂ : T2Side G L₂ V₂ Z J T M₂ e
  field : T2Field G L L₂ V V₂ Z J T S e
  coords : ∃ a b c : G → GaloisField 2 e,
    T2Heis G J V V₂ Z (GaloisField 2 e) a b c ∧ T2Tori G J Z L L₂ (GaloisField 2 e) a b c

end CFSG.CGT.PushingUpLit.A78T2
