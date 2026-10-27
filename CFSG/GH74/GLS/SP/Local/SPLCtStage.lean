module

public import CFSG.GH74.GLS.SP.Local.SPLCtDefs
public import CFSG.GH74.GLS.SP.Local.SPLStages

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local
open scoped Pointwise commutatorElement

section Stage

variable {G : Type} [Group G]

structure SPLCt0 (D : SPLNot1 G) : Prop where
  I_le_K : D.Ict ≤ D.K
  I_le_Ct : D.Ict ≤ D.Ct
  I_L2 : IVK.IsL2 ↥D.Ict (fun r => r = D.q)
  I_perf : ⁅D.Ict, D.Ict⁆ = D.Ict
  I_inf_z : D.Ict ⊓ zpowers D.z = ⊥
  CK : D.Ct ⊓ D.K = D.Ict ⊔ zpowers D.z
  CCt : D.C ⊓ D.Ct = (zpowers D.z ⊔ zpowers D.t) ⊔ (D.Ict ⊔ D.F₀)
  F₀_norm : ∀ f ∈ D.F₀, ∀ i ∈ D.Ict, f * i * f⁻¹ ∈ D.Ict
  F₀_inf : D.F₀ ⊓ D.Ict = ⊥
  F₀_faith : ∀ f ∈ D.F₀, (∀ i ∈ D.Ict, f * i = i * f) → f = 1
  F₀_odd : Odd (Nat.card ↥D.F₀)
  F_cen : ∀ f ∈ D.F, ∀ s ∈ D.S₁, f * s = s * f
  O2 : ∀ N : Subgroup G, N ≤ D.C ⊓ D.Ct → (∀ g ∈ D.C ⊓ D.Ct, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
    Odd (Nat.card ↥N) → N = ⊥
  I_comp : IsPCompIn 2 (D.C ⊓ D.Ct) D.Ict
  T₁ex : ∃ T₁ : Subgroup G, T₁ ≤ D.Ict ⊓ D.S₁ ∧ IsPGroup 2 T₁ ∧
    (∀ P : Subgroup G, P ≤ D.Ict → IsPGroup 2 P → T₁ ≤ P → P = T₁) ∧
    IVK.IsDihedralOrder ↥T₁ (2 ^ (D.n - 1))
  A_odd : Odd (Nat.card ↥D.Act)
  A_normal : ∀ c ∈ D.Ct, ∀ a ∈ D.Act, c * a * c⁻¹ ∈ D.Act
  A_comm : ∀ a ∈ D.Act, ∀ b ∈ D.Act, a * b = b * a
  A_inv : ∀ a ∈ D.Act, D.z * a * D.z⁻¹ = a⁻¹
  AI_inf : D.Act ⊓ D.Ict = ⊥

structure SPLCtU (D : SPLNot1 G) (u : G) : Prop where
  mem_I : u ∈ D.Ict
  ord : orderOf u = 2
  mem_S₁ : u ∈ D.S₁
  norm : ∀ x ∈ D.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D.z

@[expose] def SPLNot1.Eu (D : SPLNot1 G) (u : G) : Subgroup G :=
  pPrimeCoreOf 2 (D.K ⊓ centralizer ({u} : Set G))

structure SPLCenUAt (D : SPLNot1 G) (u : G) : Prop where
  prod : ∃ E₁ E₂ : Subgroup G, E₁ ⊔ E₂ = D.Eu u ∧ E₁ ⊓ E₂ = ⊥ ∧ (∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) ∧
    IsCyclic ↥E₁ ∧ IsCyclic ↥E₂ ∧ Nat.card ↥E₁ = D.e ∧ Nat.card ↥E₂ = D.e ∧
    (∀ a ∈ E₁, D.t * a * D.t⁻¹ ∈ E₂) ∧ (∀ a ∈ E₂, D.t * a * D.t⁻¹ ∈ E₁)
  O2_eq : pPrimeCoreOf 2 (D.C ⊓ centralizer ({u} : Set G)) = D.Eu u ⊔ D.F
  Eu_inf_F : D.Eu u ⊓ D.F = ⊥
  fit : ∀ Y : Subgroup G, Y ≤ D.C ⊓ centralizer ({u} : Set G) →
    (∀ c ∈ D.C ⊓ centralizer ({u} : Set G), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) → Odd (Nat.card ↥Y) →
    (∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) → Y ≤ D.Eu u
  torus : ∃ R : Subgroup G, R ≤ D.C ⊓ centralizer ({u} : Set G) ∧
    (∀ a ∈ D.Eu u, ∀ r ∈ R, a * r = r * a) ∧ IsCyclic ↥R ∧ IsPGroup 2 R ∧ Nat.card ↥R = 2 ^ (D.n - 1) ∧
    D.z ∈ R

@[expose] def SPLInCenU : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D₁ : SPLNot1 G,
    SPLSetup D₁.toSPLNot0 → SPL2Set D₁ → ∀ u : G, u ∈ D₁.S₁ → orderOf u = 2 → u ≠ D₁.z →
      D₁.t * u = u * D₁.t → (∀ x ∈ D₁.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D₁.z) → SPLCenUAt D₁ u

structure SPLCtA (D : SPLNot1 G) : Prop where
  I_normal : ∀ c ∈ D.Ct, ∀ i ∈ D.Ict, c * i * c⁻¹ ∈ D.Ict
  AI_comm : ∀ a ∈ D.Act, ∀ i ∈ D.Ict, a * i = i * a
  A_cyc : IsCyclic ↥D.Act
  A_dvd : Nat.card ↥D.Act ∣ D.e
  I_eq : D.Ict = IVK.Ez D.t

structure SPLCtT (D : SPLNot1 G) (T T₀ T₁ : Subgroup G) (y : G) : Prop where
  T_le : T ≤ D.Ct
  T_p : IsPGroup 2 T
  T_max : ∀ P : Subgroup G, P ≤ D.Ct → IsPGroup 2 P → T ≤ P → P = T
  zt_le : zpowers D.z ⊔ zpowers D.t ≤ T
  T₁_eq : T₁ = T ⊓ D.Ict
  T₁_S₁ : T₁ ≤ D.S₁
  T₁_dih : IVK.IsDihedralOrder ↥T₁ (2 ^ (D.n - 1))
  T₀_mem : ∀ c : G, c ∈ T₀ ↔ c ∈ T ∧ ∀ i ∈ D.Ict, c * i = i * c
  z_T₀ : D.z ∈ T₀
  t_T₀ : D.t ∈ T₀
  T₀_dih : IVK.IsDihedralOrder ↥T₀ (2 ^ (D.n - 1))
  T₀_T₁ : ∀ a ∈ T₀, ∀ b ∈ T₁, a * b = b * a
  T₀_inf_T₁ : T₀ ⊓ T₁ = ⊥
  y_mem : y ∈ T
  y_sq : y * y = 1
  T_eq : T = T₀ ⊔ T₁ ⊔ zpowers y
  T₀y_dih : IVK.IsDihedralOrder ↥(T₀ ⊔ zpowers y) (2 ^ D.n)
  T₁y_dih : IVK.IsDihedralOrder ↥(T₁ ⊔ zpowers y) (2 ^ D.n)
  T₀_norm : ∀ c ∈ T, ∀ a ∈ T₀, c * a * c⁻¹ ∈ T₀
  T₁_norm : ∀ c ∈ T, ∀ a ∈ T₁, c * a * c⁻¹ ∈ T₁

end Stage

end CFSG.GH74.GLS.SP.Local
