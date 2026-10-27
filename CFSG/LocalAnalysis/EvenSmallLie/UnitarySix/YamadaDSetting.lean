module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDBasic

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement Pointwise

structure Data (G : Type*) [Group G] where
  t : G
  L : Subgroup G
  S : Subgroup G
  z : G
  A₁ : Subgroup G
  A₂ : Subgroup G
  A₃ : Subgroup G
  A₄ : Subgroup G
  X₁ : Subgroup G
  X₈ : Subgroup G
  Λ : Subgroup G
  Sig : Subgroup G
  K₁ : Subgroup G
  K₂ : Subgroup G
  J : Subgroup G
  e : G
  w₂ : G
  w₂₃₂ : G
  C₂ : Subgroup G
  u₁ : G
  u₂ : G
  a₀ : G
  j₀ : G
  x₃ : G

namespace Data

variable {G : Type*} [Group G] (d : Data G)

@[expose] def H : Subgroup G := centralizer ({d.t} : Set G)

@[expose] def withT (B : Subgroup G) : Subgroup G := B ⊔ zpowers d.t

@[expose] def ZR : Subgroup G := zpowers d.z ⊔ zpowers d.t

@[expose] def NLA₃ : Subgroup G := d.L ⊓ normalizer (d.A₃ : Set G)

@[expose] def C₄ : Subgroup G := oTwo (normalizer (d.withT d.A₄ : Set G))

@[expose] def D : Subgroup G := d.C₄ ⊓ centralizer ({d.e} : Set G)

@[expose] def D₄ : Subgroup G := ⁅d.NLA₃, d.D⁆

@[expose] def V₁ : Subgroup G := d.D₄ ⊓ centralizer (d.X₁ : Set G)

@[expose] def C₀ : Subgroup G := oTwo (normalizer (d.ZR : Set G))

@[expose] def V₂ : Subgroup G := ⁅d.D₄, d.J⁆ ⊔ d.V₁

@[expose] def D₂ : Subgroup G := d.C₂ ⊓ centralizer (d.V₁ : Set G)

@[expose] def D₁ : Subgroup G :=
  centralizer (d.V₁ : Set G) ⊓ oTwo (normalizer (d.C₀ : Set G) ⊓ normalizer (d.V₁ : Set G))

end Data

variable {G : Type*} [Group G]

structure Hyp (d : Data G) : Prop where
  t_sq : d.t * d.t = 1
  t_ne_one : d.t ≠ 1
  L_le_H : d.L ≤ d.H
  H_le_normalizer_L : d.H ≤ normalizer (d.L : Set G)
  t_not_mem_L : d.t ∉ d.L
  card_le : ∀ P : Subgroup G, P ≤ d.H → IsPGroup 2 P → Nat.card P ≤ 2 ^ 17
  C₂_pGroup : IsPGroup 2 d.C₂
  C₂_le : d.C₂ ≤ normalizer (d.withT d.A₂ : Set G)
  C₂_normal : normalizer (d.withT d.A₂ : Set G) ≤ normalizer (d.C₂ : Set G)
  C₂_le_cent : d.C₂ ≤ centralizer (d.A₂ : Set G)
  C₂_inf_H : d.C₂ ⊓ d.H = d.withT d.A₂
  C₂_conj : ∀ a ∈ d.A₂, ∃ c ∈ d.C₂, c⁻¹ * d.t * c = a * d.t
  C₂_max : normalizer (d.withT d.A₂ : Set G) ⊓ centralizer (d.A₂ : Set G) ≤ d.C₂
  A₂_le_L : d.A₂ ≤ d.L
  A₃_le_L : d.A₃ ≤ d.L
  A₄_le_A₂ : d.A₄ ≤ d.A₂
  A₄_le_A₃ : d.A₄ ≤ d.A₃
  A₂_comm : ∀ a ∈ d.A₂, ∀ b ∈ d.A₂, a * b = b * a
  A₂_sq : ∀ a ∈ d.A₂, a * a = 1
  card_A₂ : Nat.card d.A₂ = 2 ^ 9
  A₃_le_cent_A₄ : d.A₃ ≤ centralizer (d.A₄ : Set G)
  card_A₃ : Nat.card d.A₃ = 2 ^ 12
  center_A₃ : d.A₃ ⊓ centralizer (d.A₃ : Set G) ≤ d.A₄
  card_A₄ : Nat.card d.A₄ = 2 ^ 4
  NHA₄_le : normalizer (d.A₄ : Set G) ⊓ d.H ≤ normalizer (d.A₃ : Set G)
  oTwo_NA₄ : ∀ P : Subgroup G, P ≤ normalizer (d.withT d.A₄ : Set G) ⊓ d.H →
    normalizer (d.withT d.A₄ : Set G) ⊓ d.H ≤ normalizer (P : Set G) → IsPGroup 2 P →
    P ≤ d.withT d.A₃
  oTwo_CA₄ : ∀ P : Subgroup G, P ≤ centralizer (d.A₄ : Set G) ⊓ d.H →
    centralizer (d.A₄ : Set G) ⊓ d.H ≤ normalizer (P : Set G) → IsPGroup 2 P →
    P ≤ d.withT d.A₃
  Λ_comm_CA₄ : ∀ l ∈ d.Λ, ∀ n ∈ centralizer (d.A₄ : Set G) ⊓ d.H, ⁅l, n⁆ ∈ d.withT d.A₃
  center_CA₄ : ∀ n ∈ centralizer (d.A₄ : Set G) ⊓ d.H,
    (∀ m ∈ centralizer (d.A₄ : Set G) ⊓ d.H, ⁅n, m⁆ ∈ d.withT d.A₃) → n ^ 3 ∈ d.withT d.A₃
  Λ_le_L : d.Λ ≤ d.L
  Λ_le_normalizer : d.Λ ≤ normalizer (d.A₄ : Set G)
  A₄_le_comm : d.A₄ ≤ ⁅d.A₄, d.Λ⁆
  e_mem_L : d.e ∈ d.L
  e_pow : d.e ^ 3 = 1
  e_cent_A₄ : d.e ∈ centralizer (d.A₄ : Set G)
  e_norm_A₃ : d.e ∈ normalizer (d.A₃ : Set G)
  A₃_cent_e : d.A₃ ⊓ centralizer ({d.e} : Set G) ≤ d.A₄
  A₃_le_comm_e : d.A₃ ≤ ⁅d.A₃, zpowers d.e⁆ ⊔ d.A₄
  A₃_irred : ∀ B : Subgroup G, d.A₄ ≤ B → B ≤ d.A₃ → d.NLA₃ ≤ normalizer (B : Set G) →
    B = d.A₄ ∨ B = d.A₃
  NLA₃_le : d.NLA₃ ≤ normalizer (d.A₄ : Set G)
  NLA₃_le_gen : d.NLA₃ ≤ d.Λ ⊔ d.Sig ⊔ d.A₃
  Λ_le_NA₃ : d.Λ ≤ normalizer (d.A₃ : Set G)
  Sig_le_L : d.Sig ≤ d.L
  Sig_le_NA₃ : d.Sig ≤ normalizer (d.A₃ : Set G)
  Sig_le_cent_A₄ : d.Sig ≤ centralizer (d.A₄ : Set G)
  Λ_comm_Sig : ∀ l ∈ d.Λ, ∀ s ∈ d.Sig, l * s = s * l
  X₁_le_Λ : d.X₁ ≤ d.Λ
  card_X₁ : Nat.card d.X₁ = 4
  odd_index_X₁ : Odd (d.X₁.relIndex d.Λ)
  u₁_mem : d.u₁ ∈ d.X₁
  u₂_mem : d.u₂ ∈ d.X₁
  X₁_le_closure : d.X₁ ≤ closure {d.u₁, d.u₂}
  u₁_sq : d.u₁ * d.u₁ = 1
  u₂_sq : d.u₂ * d.u₂ = 1
  u₁_comm_u₂ : d.u₁ * d.u₂ = d.u₂ * d.u₁
  a₀_mem : d.a₀ ∈ d.A₄
  A₄_le_closure : d.A₄ ≤ closure ((fun x => x * d.a₀ * x⁻¹) '' (d.X₁ : Set G))
  norm_a₀ : d.a₀ * (d.u₁ * d.a₀ * d.u₁⁻¹) * (d.u₂ * d.a₀ * d.u₂⁻¹) *
    ((d.u₁ * d.u₂) * d.a₀ * (d.u₁ * d.u₂)⁻¹) = d.z
  A₄_cent_X₁ : d.A₄ ⊓ centralizer (d.X₁ : Set G) ≤ zpowers d.z
  hom_wedge_A₄ : ∀ β : G → G → G, (∀ a ∈ d.A₄, ∀ b ∈ d.A₄, β a b ∈ d.A₄) →
    (∀ a ∈ d.A₄, ∀ b ∈ d.A₄, ∀ c ∈ d.A₄, β (a * b) c = β a c * β b c) →
    (∀ a ∈ d.A₄, ∀ b ∈ d.A₄, ∀ c ∈ d.A₄, β a (b * c) = β a b * β a c) →
    (∀ a ∈ d.A₄, β a a = 1) →
    (∀ l ∈ d.Λ, ∀ a ∈ d.A₄, ∀ b ∈ d.A₄, β (l * a * l⁻¹) (l * b * l⁻¹) = l * β a b * l⁻¹) →
    ∀ a ∈ d.A₄, ∀ b ∈ d.A₄, β a b = 1
  z_mem_A₄ : d.z ∈ d.A₄
  z_ne_one : d.z ≠ 1
  z_cent_X₁ : d.z ∈ centralizer (d.X₁ : Set G)
  A₁_le_L : d.A₁ ≤ d.L
  A₁_le : d.A₁ ≤ d.X₁ ⊔ d.A₃
  z_mem_A₁ : d.z ∈ d.A₁
  card_A₁ : Nat.card d.A₁ = 2 ^ 9
  center_A₁ : d.A₁ ⊓ centralizer (d.A₁ : Set G) ≤ zpowers d.z
  CHz_le : centralizer ({d.z} : Set G) ⊓ d.H ≤ normalizer (d.A₁ : Set G)
  CH_A₁ : centralizer (d.A₁ : Set G) ⊓ d.H ≤ d.ZR
  oTwo_CHz : ∀ P : Subgroup G, P ≤ centralizer ({d.z} : Set G) ⊓ d.H →
    centralizer ({d.z} : Set G) ⊓ d.H ≤ normalizer (P : Set G) → IsPGroup 2 P →
    P ≤ d.withT d.A₁
  K₁_le_L : d.K₁ ≤ d.L
  K₁_cent_z : d.K₁ ≤ centralizer ({d.z} : Set G)
  K₁_perfect : d.K₁ ≤ ⁅d.K₁, d.K₁⁆
  j₀_mem_L : d.j₀ ∈ d.L
  J_eq : d.J = zpowers d.j₀
  j₀_pow : d.j₀ ^ 3 = 1
  j₀_u₁ : d.j₀ * d.u₁ * d.j₀⁻¹ = d.u₂
  j₀_u₂ : d.j₀ * d.u₂ * d.j₀⁻¹ = d.u₁ * d.u₂
  j₀_norm_A₃ : d.j₀ ∈ normalizer (d.A₃ : Set G)
  j₀_comm_z : d.j₀ * d.z = d.z * d.j₀
  comm_A₄_J : ⁅d.A₄, d.J⁆ = d.X₈
  A₄_le_cent_J_sup : d.A₄ ≤ (d.A₄ ⊓ centralizer (d.J : Set G)) ⊔ d.X₈
  card_X₈ : Nat.card d.X₈ = 4
  X₈_inf_z : d.X₈ ⊓ zpowers d.z = ⊥
  X₈_le_A₁ : d.X₈ ≤ d.A₁
  comm_X₁_Z₂ : ∀ x ∈ d.X₁, ∀ b ∈ d.X₈ ⊔ zpowers d.z, x * b * x⁻¹ * b⁻¹ ∈ zpowers d.z
  A₄_comm_X₁ : ∀ x ∈ d.X₁, x ≠ 1 → ∀ a ∈ d.A₄, x * a * x⁻¹ * a⁻¹ ∈ zpowers d.z →
    a ∈ d.X₈ ⊔ zpowers d.z
  x₃_mem_K₁ : d.x₃ ∈ d.K₁
  x₃_mem_Sig : d.x₃ ∈ d.Sig
  A₂_le_x₃ : d.A₂ ≤ zpowers d.x₃ ⊔ d.A₃
  A₄_le_orbit_z : d.A₄ ≤ closure ((fun l => l * d.z * l⁻¹) '' (d.Λ : Set G))
  A₁_comm : ∀ a ∈ d.A₁, ∀ b ∈ d.A₁, a * b * a⁻¹ * b⁻¹ ∈ zpowers d.z
  card_sing : {S : Set G | ∃ a ∈ d.A₁, a * a = 1 ∧ S = a • (zpowers d.z : Set G)}.ncard = 136
  K₁_trans : ∀ a ∈ d.A₁, a * a = 1 → a ∉ zpowers d.z → ∀ b ∈ d.A₁, b * b = 1 →
    b ∉ zpowers d.z → ∃ k ∈ d.K₁, (k * a * k⁻¹)⁻¹ * b ∈ zpowers d.z
  card_CHz : Nat.card (centralizer ({d.z} : Set G) ⊓ d.H : Subgroup G) ∣ 2 ^ 17 * 3 ^ 5 * 5

end CFSG.EvenSmallLie.UnitarySix.YamadaD
