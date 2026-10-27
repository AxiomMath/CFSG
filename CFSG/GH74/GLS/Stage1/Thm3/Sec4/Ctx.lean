module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Pm (S K₁ K₂ : Subgroup G) : Subgroup G := S ⊓ (K₁ ⊔ K₂)

@[expose] def Qm (O : Subgroup G → Subgroup G) (S K₁ K₂ : Subgroup G) : Subgroup G :=
  S ⊓ secCent (K₁ ⊔ K₂) (O (K₁ ⊔ K₂))

@[expose] def Rm (O : Subgroup G → Subgroup G) (S K₁ K₂ : Subgroup G) : Subgroup G :=
  Pm S K₁ K₂ ⊔ Qm O S K₁ K₂

@[expose] def H4A (O : Subgroup G → Subgroup G) (z : G) (S K₁ K₂ : Subgroup G) : Prop :=
  ∀ t ∈ Rm O S K₁ K₂, IsConj z t → t = z

@[expose] def Intch (t : G) (K₁ K₂ : Subgroup G) : Prop := cj K₁ t = K₂ ∧ cj K₂ t = K₁

structure M4 (O : Subgroup G → Subgroup G) (FA : G → Subgroup G → Prop) (SD : Subgroup G → Prop)
    (z : G) (S K₁ K₂ : Subgroup G) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  S_syl : Syl2In S (centralizer ({z} : Set G))
  S_top : Syl2In S ⊤
  K₁_le : K₁ ≤ centralizer ({z} : Set G)
  K₂_le : K₂ ≤ centralizer ({z} : Set G)
  cs₁ : K₂ ≤ secCent K₁ (O K₁)
  cs₂ : K₁ ≤ secCent K₂ (O K₂)
  perm : ∀ c ∈ centralizer ({z} : Set G),
    (cj K₁ c = K₁ ∧ cj K₂ c = K₂) ∨ (cj K₁ c = K₂ ∧ cj K₂ c = K₁)
  core : ∀ K, (K = K₁ ∨ K = K₂) → IsOddCore K (O K)
  coreK : IsOddCore (K₁ ⊔ K₂) (O (K₁ ⊔ K₂))
  nonab : ∀ K, (K = K₁ ∨ K = K₂) → ∃ a ∈ K, ∃ b ∈ K, ⁅a, b⁆ ∉ O K
  rk : ∀ K, (K = K₁ ∨ K = K₂) → Rk1 K
  zs : ∀ K, (K = K₁ ∨ K = K₂) → Nat.card ↥(S ⊓ ZsM O K) = 2 ∧ 8 ≤ Nat.card ↥(S ⊓ K)
  hb : Syl2In (zpowers z) (ZsM O (K₁ ⊔ K₂))
  hc : ∀ t ∈ centralizer ({z} : Set G), IsConj z t → t ∉ ZsM O (K₁ ⊔ K₂) →
    ∀ K, (K = K₁ ∨ K = K₂) → Rk1 (centralizer ({z, t} : Set G) ⊓ secCent K (O K))
  he : ∀ t ∈ centralizer ({z} : Set G), IsConj z t → t ∉ ZsM O (K₁ ⊔ K₂) →
    ∀ K, (K = K₁ ∨ K = K₂) → ¬ FA t K

structure M42 (O : Subgroup G → Subgroup G) (FA : G → Subgroup G → Prop) (SD : Subgroup G → Prop)
    (z : G) (S K₁ K₂ : Subgroup G) : Prop
    extends M4 O FA SD z S K₁ K₂ where
  f31a : ∀ u v : G, u ∈ K₁ ⊔ K₂ → v ∈ K₁ ⊔ K₂ → u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 →
    u ≠ z → v ≠ z → ∃ k ∈ K₁ ⊔ K₂, k * u * k⁻¹ = v

structure M43 (O : Subgroup G → Subgroup G) (FA : G → Subgroup G → Prop) (SD : Subgroup G → Prop)
    (z : G) (S K₁ K₂ : Subgroup G) : Prop
    extends M4 O FA SD z S K₁ K₂ where
  rec1b : ∀ t g : G, g⁻¹ * z * g = t → t ∈ centralizer ({z} : Set G) →
    ∀ J L, (J = K₁ ∨ J = K₂) → (L = K₁ ∨ L = K₂) → t ∈ normalizer (J : Set G) →
      ∀ a ∈ J, IsPGroup 2 (zpowers a) → a ∉ zpowers z → a * t = t * a →
        a ∈ normalizer (cj L g : Set G)
  f19 : ∀ K, (K = K₁ ∨ K = K₂) → ∀ t ∈ S, orderOf t = 2 → t ∈ normalizer (K : Set G) → ¬ FA t K →
    SD (Pm S K₁ K₂ ⊓ K ⊔ zpowers t) ∨
      ∃ u ∈ K, t * u = u * t ∧ 4 ≤ orderOf u ∧ 2 * orderOf u = Nat.card ↥(Pm S K₁ K₂ ⊓ K)
  f12f : ∀ K, (K = K₁ ∨ K = K₂) → ∀ y : G, IsPGroup 2 (zpowers y) → y ∈ normalizer (K : Set G) →
    orderOf (y * y) = 2 → ¬ FA (y * y) K → ∃ k ∈ K, y * y * k⁻¹ ∈ secCent K (O K)

structure M44 (O : Subgroup G → Subgroup G) (FA : G → Subgroup G → Prop) (SD : Subgroup G → Prop)
    (z : G) (S K₁ K₂ : Subgroup G) : Prop
    extends M43 O FA SD z S K₁ K₂ where
  fsd : ∀ (P : Subgroup G) (t : G), IsPGroup 2 ↥P → z ∈ P → (∀ x ∈ P, x * z = z * x) →
    (∀ x ∈ P, x * x = 1 → x = 1 ∨ x = z) → t * t = 1 → t ∉ P → (∀ x ∈ P, t * x * t ∈ P) →
    SD (P ⊔ zpowers t) →
      (∃ u₁ ∈ P, u₁ * u₁ = z ∧ t * u₁ * t = u₁⁻¹ ∧ ∃ x ∈ P, x⁻¹ * t * x = t * u₁) ∧
        ∃ y ∈ P, y⁻¹ * t * y = t * z

structure M45 (O : Subgroup G → Subgroup G) (FA : G → Subgroup G → Prop) (SD : Subgroup G → Prop)
    (z : G) (S K₁ K₂ : Subgroup G) : Prop
    extends M42 O FA SD z S K₁ K₂ where
  rec2 : ∀ t g : G, g⁻¹ * z * g = t → t ∈ centralizer ({z} : Set G) →
    ∀ J L, (J = K₁ ∨ J = K₂) → (L = K₁ ∨ L = K₂) → z ∈ normalizer (cj J g : Set G) →
      t ∈ normalizer (L : Set G)
  fbal : H4A O z S K₁ K₂ → ∀ t ∈ S, IsConj z t → t ≠ z → Intch t K₁ K₂ →
    ∀ u₁ ∈ K₁, u₁ ∈ S → u₁ * u₁ = z → IsConj (u₁ * (t * u₁ * t)) (t * (u₁ * (t * u₁ * t)))

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
