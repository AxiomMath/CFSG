module

public import CFSG.GH74.Uniqueness.SU.SU13TB1Core
public import CFSG.GH74.Uniqueness.SU.SU4Stmts
public import CFSG.GH74.Uniqueness.SU.SU13TB0Syl

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

structure Elts (G : Type) [Group G] (z : G) where
  s₁ : G
  s₂ : G
  s₃ : G
  t : G
  s₁_comm : s₁ * z = z * s₁
  s₂_comm : s₂ * z = z * s₂
  s₃_comm : s₃ * z = z * s₃
  s₁_ord : orderOf s₁ = 3
  s₂_ord : orderOf s₂ = 3
  s₃_ord : orderOf s₃ = 3
  t_comm : t * z = z * t
  t_ord : orderOf t = 2
  t_ne : t ≠ z
  t_s₂ : t * s₂ = s₂ * t
  t_s₁ : t * s₁ * t⁻¹ = s₁⁻¹
  class3 : ∀ u : G, u * z = z * u → orderOf u = 3 →
    ∃ h : G, h * z = z * h ∧ (h * u * h⁻¹ = s₁ ∨ h * u * h⁻¹ = s₂ ∨ h * u * h⁻¹ = s₃)
  class2 : ∀ u v : G, u * z = z * u → v * z = z * v → orderOf u = 2 → orderOf v = 2 → u ≠ z →
    v ≠ z → ∃ h : G, h * z = z * h ∧ h * u * h⁻¹ = v

structure FPart {G : Type} [Group G] (z : G) (e : Elts G z) where
  F : Subgroup G
  F_comm : ∀ f ∈ F, f * z = z * f
  z_mem : z ∈ F
  F_s₁ : ∀ f ∈ F, f * e.s₁ = e.s₁ * f
  cent : centralizer ({e.s₁} : Set G) ⊓ centralizer ({z} : Set G) = zpowers e.s₁ ⊔ F
  F_noOdd : ∀ N : Subgroup G, N ≤ F → (∀ f ∈ F, ∀ n ∈ N, f * n * f⁻¹ ∈ N) → Odd (Nat.card N) → N = ⊥
  F_socle : ∀ N : Subgroup G, N ≤ F → (∀ f ∈ F, ∀ n ∈ N, f * n * f⁻¹ ∈ N) → N ≠ ⊥ → z ∈ N
  T₁ : Subgroup G
  T₁_syl : IsSylowIn (centralizer ({e.s₁} : Set G) ⊓ centralizer ({z} : Set G)) T₁
  T₁_z : z ∈ T₁
  T₁_uniq : ∀ y ∈ T₁, orderOf y = 2 → y = z
  T₁_quat : ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥T₁ ≃* QuaternionGroup (2 ^ k))

structure FPart10 {G : Type} [Group G] (z : G) (e : Elts G z) extends FPart z e where
  F_five : ∃ u ∈ F, orderOf u = 5
  F_seven : ∃ u ∈ F, orderOf u = 7

structure P3Part {G : Type} [Group G] (z : G) (e : Elts G z) : Prop where
  syl : IsSylowIn (centralizer ({e.s₃} : Set G) ⊓ centralizer ({z} : Set G)) (zpowers z)

structure MPart10 {G : Type} [Group G] [Finite G] (z : G) (e : Elts G z) : Prop where
  card : Nat.card ↥(centralizer ({e.s₂} : Set G) ⊓ centralizer ({z} : Set G)) = 432
  gl : Nonempty (Mbar (centralizer ({e.s₂} : Set G) ⊓ centralizer ({z} : Set G)) ≃*
    GL (Fin 2) (ZMod 3))
  cent_t : ∀ x ∈ oc (centralizer ({e.s₂} : Set G) ⊓ centralizer ({z} : Set G)), e.t * x = x * e.t →
    x ∈ zpowers e.s₂

structure EPart10 {G : Type} [Group G] [Finite G] (z : G) (e : Elts G z) : Prop where
  ex : ∃ E Es : Subgroup G, e.s₁ ∈ E ∧ E ≤ Es ∧ Nat.card E = 27 ∧
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ IsPGroup 3 Es ∧ Nat.card Es = 81 ∧
    (∀ x ∈ Es, x * z = z * x) ∧
    (∀ R : Subgroup G, (∀ x ∈ R, x * z = z * x) → IsPGroup 3 R → Es ≤ R → R = Es) ∧
    (∀ A : Subgroup G, A ≤ Es → Nat.card A = 27 → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = E) ∧
    (centralizer (E : Set G) ⊓ centralizer ({z} : Set G) = E ⊔ zpowers z)

structure Loc10 (G : Type) [Group G] [Finite G] (z : G) where
  e : Elts G z
  f : FPart10 z e
  p3 : P3Part z e
  m : MPart10 z e
  E : EPart10 z e

end CFSG.GH74.Uniqueness.SU.SU13
