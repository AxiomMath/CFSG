module

public import CFSG.GH74.Uniqueness.SU.SU13Data

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

structure Elts9 {G : Type} [Group G] (z : G) (e : Elts G z) where
  s₄ : G
  x : G
  s₄_comm : s₄ * z = z * s₄
  s₄_ord : orderOf s₄ = 3
  x_comm : x * z = z * x
  x_ord : orderOf x = 2
  t_s₄ : e.t * s₄ * e.t⁻¹ = s₄⁻¹
  x_s₁ : x * e.s₁ * x⁻¹ = e.s₁⁻¹
  x_s₂ : x * e.s₂ * x⁻¹ = e.s₂⁻¹
  x_s₄ : x * s₄ = s₄ * x
  s₄_class : ∃ h : G, h * z = z * h ∧ h * s₄ * h⁻¹ = e.s₂

structure FPart9 {G : Type} [Group G] (z : G) (e : Elts G z) extends FPart z e where
  F_card : Nat.card ↥F = 720

@[expose] def NHE {G : Type} [Group G] (E : Subgroup G) (z : G) : Subgroup G :=
  normalizer (E : Set G) ⊓ centralizer ({z} : Set G)

structure EPart9 {G : Type} [Group G] [Finite G] (z : G) (e : Elts G z) (e9 : Elts9 z e) (f : FPart z e) where
  E : Subgroup G
  Es : Subgroup G
  D : Subgroup G
  S₂ : Subgroup G
  r : G
  s₁_mem : e.s₁ ∈ E
  s₂_mem : e.s₂ ∈ E
  s₄_mem : e9.s₄ ∈ E
  E_gen : ∀ g ∈ E, ∃ i j k : ℤ, g = e.s₁ ^ i * e.s₂ ^ j * e9.s₄ ^ k
  E_card : Nat.card ↥E = 27
  E_abel : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  E_exp : ∀ a ∈ E, a ^ 3 = 1
  Es_ge : E ≤ Es
  Es_p : IsPGroup 3 Es
  Es_card : Nat.card ↥Es = 81
  Es_comm : ∀ x ∈ Es, x * z = z * x
  Es_max : ∀ R : Subgroup G, (∀ x ∈ R, x * z = z * x) → IsPGroup 3 R → Es ≤ R → R = Es
  E_unique : ∀ A : Subgroup G, A ≤ Es → Nat.card ↥A = 27 → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = E
  cent : centralizer (E : Set G) ⊓ centralizer ({z} : Set G) = E ⊔ zpowers z
  t_norm : ∀ a ∈ E, e.t * a * e.t⁻¹ ∈ E
  x_norm : ∀ a ∈ E, e9.x * a * e9.x⁻¹ ∈ E
  noOdd : ∀ N : Subgroup G, N ≤ NHE E z → (∀ g ∈ NHE E z, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → Odd (Nat.card ↥N) → N ≤ E
  irred : ∀ P : Subgroup G, P ≤ E → e.s₁ ∈ P → (∀ g ∈ NHE E z, ∀ p ∈ P, g * p * g⁻¹ ∈ P) → P = E
  invClass : ∀ u ∈ NHE E z, orderOf u = 2 → u ≠ z → ∃ g ∈ NHE E z, g * e.t * g⁻¹ = u
  S₂_syl : IsSylowIn (NHE E z) S₂
  S₂_z : z ∈ S₂
  S₂_cen : ∀ y ∈ S₂, orderOf y = 2 → (∀ s ∈ S₂, s * y = y * s) → y = z
  D_le_F : D ≤ f.F
  D_le_E : D ≤ E
  D_card : Nat.card ↥D = 9
  E_eq : ∀ g ∈ E, ∃ i : ℤ, ∃ d ∈ D, g = e.s₁ ^ i * d
  r_mem : r ∈ f.F
  r_ord : orderOf r = 8
  r_pow : r ^ 4 = z
  r_norm : ∀ d ∈ D, r * d * r⁻¹ ∈ D
  t_D : ∀ d ∈ D, e.t * d * e.t⁻¹ ∈ D
  t_r : e.t * r * e.t⁻¹ ∈ zpowers r
  t_r_ne : e.t * r * e.t⁻¹ ≠ r

structure MPart9 {G : Type} [Group G] [Finite G] (z : G) (e : Elts G z) (E : Subgroup G) : Prop where
  card : Nat.card ↥(centralizer ({e.s₂} : Set G) ⊓ centralizer ({z} : Set G)) = 108
  E_le : E ≤ centralizer ({e.s₂} : Set G) ⊓ centralizer ({z} : Set G)
  oc_eq : oc (centralizer ({e.s₂} : Set G) ⊓ centralizer ({z} : Set G)) = E
  kl : Nonempty (Mbar (centralizer ({e.s₂} : Set G) ⊓ centralizer ({z} : Set G)) ≃*
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  cent_t : ∀ x ∈ E, e.t * x = x * e.t → x ∈ zpowers e.s₂

structure Loc9 (G : Type) [Group G] [Finite G] (z : G) where
  e : Elts G z
  e9 : Elts9 z e
  f : FPart9 z e
  p3 : P3Part z e
  E : EPart9 z e e9 f.toFPart
  m : MPart9 z e E.E

end CFSG.GH74.Uniqueness.SU.SU13
