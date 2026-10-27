module

public import CFSG.GH74.GLS.SP.Local.SPLNotation
public import CFSG.GH74.GLS.IVK.Statements.Sec4
public import CFSG.GH74.GLS.SP.Local.Defs
public import CFSG.GH74.GLS.SP.Model

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def IsEAb (p : ℕ) (X : Subgroup G) : Prop :=
  (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) ∧ ∀ x ∈ X, x ^ p = 1

@[expose] def Normalizes (H X : Subgroup G) : Prop := ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X

structure SPLSetup (D : SPLNot0 G) : Prop where
  prime : D.p.Prime
  p_ne_two : D.p ≠ 2
  q_pow : ∃ k : ℕ, 1 ≤ k ∧ D.q = D.p ^ k
  q_ge : 5 ≤ D.q
  comps : LUComps G D.q D.z D.K₁ D.K₂
  syl : SPSyl G D.z D.S D.K₁ D.K₂ D.t
  O2 : pPrimeCoreOf 2 (Cz D.z) = ⊥
  gen : ∀ c ∈ Cz D.z, ∃ k ∈ D.K, ∃ s ∈ (D.S : Subgroup G), ∃ y ∈ D.F, c = k * s * y

structure SPL2Set (D : SPLNot1 G) : Prop where
  cen_S₁ : centralizer (D.S₁ : Set G) = zpowers D.z ⊔ D.F
  F_inf_K : D.F ⊓ D.K = ⊥
  h₁_mem : D.h₁ ∈ D.K₁
  h₁_ord : orderOf D.h₁ = D.q - 1
  H_inter : D.H₁ ⊓ D.H₂ = zpowers D.z
  w₁_mem : D.w₁ ∈ D.K₁
  w₁_sq : D.w₁ * D.w₁ = D.z
  w₁_inv : ∀ h ∈ D.H₁, D.w₁ * h * D.w₁⁻¹ = h⁻¹
  nbhd : normalizer (D.H₁ : Set G) ⊓ D.K₁ = D.H₁ ⊔ zpowers D.w₁
  H_sylow : ¬ 2 ∣ (D.H ⊓ D.S₁).relIndex D.H
  w₁_mem_S₁ : D.w₁ ∈ D.S₁
  F_norm_H : Normalizes D.F D.H
  norm_le_C : normalizer (D.H : Set G) ≤ D.C

structure SPL2Ct (D : SPLNot2 G) : Prop where
  I_eq : D.I = IVK.Ez D.t
  I_der : D.I = ⁅centralizer ({D.t} : Set G) ⊓ D.K, centralizer ({D.t} : Set G) ⊓ D.K⁆
  I_L2 : IVK.IsL2 ↥D.I (fun r => r = D.q)
  A_eq : D.A = pPrimeCoreOf 2 D.Ct
  A_cyc : IsCyclic ↥D.A
  A_card : Nat.card ↥D.A = D.e
  A_inv : ∀ a ∈ D.A, D.z * a * D.z⁻¹ = a⁻¹
  AI_inf : D.A ⊓ D.I = ⊥
  AI_comm : ∀ a ∈ D.A, ∀ i ∈ D.I, a * i = i * a
  Ct_eq : D.Ct = D.I ⊔ D.A ⊔ D.F₀ ⊔ zpowers D.x ⊔ zpowers D.z
  xz_dih : IVK.IsDihedralOrder ↥(zpowers D.x ⊔ zpowers D.z) (2 ^ D.n)
  x_ord : orderOf D.x = 2 ^ (D.n - 1)
  x_pow : D.x ^ (2 ^ (D.n - 2)) = D.t
  x_norm : D.x ∈ normalizer ((D.H₀ ⊔ zpowers D.w : Subgroup G) : Set G)
  x2_cen : ∀ y ∈ D.I ⊔ D.A, D.x ^ 2 * y = y * D.x ^ 2
  quot : ∃ _ : ((zpowers (D.x ^ 2)).subgroupOf (D.I ⊔ zpowers D.x)).Normal,
    IVK.IsPGL2 (↥(D.I ⊔ zpowers D.x) ⧸ (zpowers (D.x ^ 2)).subgroupOf (D.I ⊔ zpowers D.x))
      (fun r => r = D.q)
  F_eq : D.F ≤ D.Ct
  A_x : ∀ a ∈ D.A, a * D.x = D.x * a
  N_C : ∀ A₀ : Subgroup G, A₀ ≤ D.A → A₀ ≠ ⊥ → normalizer (A₀ : Set G) ⊓ D.C = D.C ⊓ D.Ct
  cen_I : centralizer (D.I : Set G) ⊓ D.Ct = D.A ⊔ (zpowers (D.x ^ 2) ⊔ zpowers D.z)

structure SPL2Ord (D : SPLNot0 G) : Prop where
  card_G : 2 * Nat.card G = D.q ^ 4 * (D.q ^ 2 - 1) * (D.q ^ 4 - 1) * Nat.card ↥D.F
  card_sylow : ∀ T : Sylow D.p G,
    Nat.card ↥T = D.q ^ 4 * D.p ^ (Nat.card ↥D.F).factorization D.p

structure SPL3A (D : SPLNot3 G) : Prop where
  a_z : D.a⁻¹ * D.z * D.a = D.z * D.t
  a_u : ∃ u ∈ D.H₀, u * u = 1 ∧ D.a * D.a = u * D.t ∧ D.a⁻¹ * D.w * D.a = u * D.w
  a_H₀ : ∀ h ∈ D.H₀, D.a⁻¹ * h * D.a ∈ D.H₀

structure SPL3X (D : SPLNot3 G) : Prop where
  X₁_le : D.X₁ ≤ D.K₁
  X₁'_le : D.X₁' ≤ D.K₁
  X₁_card : Nat.card ↥D.X₁ = D.q
  X₁'_card : Nat.card ↥D.X₁' = D.q
  X₁_eab : IsEAb D.p D.X₁
  X₁'_eab : IsEAb D.p D.X₁'
  X₁_ne : D.X₁ ≠ D.X₁'
  K₁_eq : D.K₁ = D.X₁ ⊔ D.X₁'
  X₁'_eq : D.X₁' = conjBy D.w₁ D.X₁
  H_X₁ : Normalizes D.H D.X₁
  H_X₁' : Normalizes D.H D.X₁'
  two : ∀ W : Subgroup G, W ≤ D.K₁ → IsPGroup D.p ↥W → Nat.card ↥W = D.q → Normalizes D.H W →
    W = D.X₁ ∨ W = D.X₁'
  F_X₁ : Normalizes D.F D.X₁
  F_X₁' : Normalizes D.F D.X₁'
  Y₁_eq : D.Y₁ = ⁅D.X, zpowers D.t⁆
  Y₁_le : D.Y₁ ≤ D.X
  Y₁_card : Nat.card ↥D.Y₁ = D.q
  Y₁_eab : IsEAb D.p D.Y₁
  Y₁_inv : ∀ y ∈ D.Y₁, D.t * y * D.t⁻¹ = y⁻¹

structure SPL3Aa (D : SPLNot3 G) : Prop where
  a_mem : D.a ∈ D.Ct
  a_ord : orderOf D.a = 4
  a_facts : SPL3A D
  a_Y₀ : conjBy D.a (centralizer ({D.t} : Set G) ⊓ D.X) = centralizer ({D.t} : Set G) ⊓ D.X

structure SPL3R2 (D : SPLNot3 G) : Prop where
  X₁_X₃ : ∀ x ∈ D.X₁, ∀ y ∈ D.X₃, x * y = y * x
  R₂_prod : (D.R₂ : Set G) = (D.X₂ : Set G) * (D.X₃ : Set G) * (D.X₄ : Set G)
  H_X₃ : Normalizes D.H D.X₃
  R₂_normal : D.M₂ ≤ normalizer (D.R₂ : Set G)
  R₂_card : Nat.card ↥D.R₂ = D.q ^ 3
  R₂_center : (center ↥D.R₂).map D.R₂.subtype = D.X₂
  R₂_comm : ⁅D.R₂, D.R₂⁆ = D.X₂

structure SPL3M2 (D : SPLNot3 G) : Prop extends SPL3X D, SPL3Aa D, SPL3R2 D where
  z_X₃ : ∀ x ∈ D.X₃, D.z * x * D.z⁻¹ = x⁻¹
  t_X₃ : conjBy D.t D.X₃ = D.X₃
  R₂_nonab : ∃ x ∈ D.R₂, ∃ y ∈ D.R₂, x * y ≠ y * x
  P_pGroup : IsPGroup D.p ↥D.P
  P_card : Nat.card ↥D.P = D.q ^ 4

structure SPL3M1 (D : SPLNot4 G) : Prop where
  J_le : D.J ≤ D.K
  J_L2 : IVK.IsL2 ↥D.J (fun r => r = D.q)
  Y₁_le : D.Y₁ ≤ D.J
  Y₁_syl : ¬ D.p ∣ D.Y₁.relIndex D.J
  NJ_Y₁ : normalizer (D.Y₁ : Set G) ⊓ D.J = D.Y₁ ⊔ D.H₀
  NJ_H₀ : normalizer (D.H₀ : Set G) ⊓ D.J = D.H₀ ⊔ zpowers (D.z * D.w)
  M₁_eq : (D.M₁ : Set G) = (D.B : Set G) ∪ (D.B : Set G) * {D.t} * (D.B : Set G)
  tBt : ¬ conjBy D.t D.B ≤ D.B
  B_inf_N : D.B ⊓ (D.H ⊔ zpowers D.t) = D.H
  R₁_normal : D.M₁ ≤ normalizer (D.R₁ : Set G)
  R₁_eab : IsEAb D.p D.R₁
  R₁_card : Nat.card ↥D.R₁ = D.q ^ 3
  J₁_le : D.J₁ ≤ D.M₁
  R₁J₁_normal : D.M₁ ≤ normalizer ((D.R₁ ⊔ D.J₁ : Subgroup G) : Set G)
  M₁_eq_RJH : D.M₁ = D.R₁ ⊔ D.J₁ ⊔ D.H
  M₁_eq_BJ : D.M₁ = D.B ⊔ D.J₁
  H_split : D.H₁ ⊓ D.H₀ = ⊥ ∧ D.H₁ ⊔ D.H₀ = D.H
  H₀_card : Nat.card ↥D.H₀ = (D.q - 1) / 2
  H₀_cen : ∀ i ∈ D.H₀, ∀ j ∈ D.J₁, ⁅i, j⁆ ∈ D.R₁
  bruhat₁ : ∀ y ∈ conjBy D.t D.X₄, y ≠ 1 →
    y ∈ (D.X₄ : Set G) * (D.H : Set G) * {D.t} * (D.X₄ : Set G)

namespace SPLNot3

variable (D : SPLNot3 G)

@[expose] def L42 : Prop :=
  ∀ Z : Subgroup G, Z ≤ D.P → Normalizes D.H Z →
    ∀ l : List ℤ, (l.Pairwise (· < ·) ∨ l.Pairwise (· > ·)) →
      (∀ i, i ∈ l ↔ (1 ≤ i ∧ i ≤ 4) ∧ D.root i ≤ Z) →
      (Z : Set G) = chainProd D.root l ∧ Nat.card ↥Z = (l.map fun i => Nat.card ↥(D.root i)).prod

@[expose] def CH_diff : Prop :=
  (∀ i j : ℤ, 1 ≤ i → i ≤ 4 → 1 ≤ j → j ≤ 4 → i ≠ j →
    centralizer (D.root i : Set G) ⊓ D.H ≠ centralizer (D.root j : Set G) ⊓ D.H) ∧
  D.P ⊓ conjBy (D.w₁ * D.w₂) D.P = ⊥

end SPLNot3

structure SPLStage4 (D : SPLNot4 G) : Prop where
  setup : SPLSetup D.toSPLNot0
  set : SPL2Set D.toSPLNot1
  ct : SPL2Ct D.toSPLNot2
  ord : SPL2Ord D.toSPLNot0
  m2 : SPL3M2 D.toSPLNot3
  m1 : SPL3M1 D

@[expose] def SPLIsoStmt (D : SPLNot3 G) (Fq : Type) [Field Fq] [Finite Fq] (hF : 4 ≤ Nat.card Fq) :
    Prop :=
  ∃ φ : ↥D.P ≃* (SP.modelSystem Fq hF).U, ∀ i : ℤ, 1 ≤ i → i ≤ 4 → ∀ x : ↥D.P,
    (x : G) ∈ D.root i ↔
      ((φ x : (SP.modelSystem Fq hF).U) : StatedProj (StatedSp 2 Fq)) ∈ (SP.modelSystem Fq hF).root i

@[expose] def SPLLeafSet : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D₀ : SPLNot0 G, SPLSetup D₀ →
    ∃ D : SPLNot1 G, D.toSPLNot0 = D₀ ∧ SPL2Set D

@[expose] def SPLLeafOrd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D : SPLNot2 G,
    SPLSetup D.toSPLNot0 → SPL2Set D.toSPLNot1 → SPL2Ct D → SPL2Ord D.toSPLNot0

@[expose] def SPLLeafM2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D₂ : SPLNot2 G,
    SPLSetup D₂.toSPLNot0 → SPL2Set D₂.toSPLNot1 → SPL2Ct D₂ → SPL2Ord D₂.toSPLNot0 →
      ∃ D : SPLNot3 G, D.toSPLNot2 = D₂ ∧ SPL3M2 D

@[expose] def SPLLeafIso : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D : SPLNot4 G, SPLStage4 D →
    D.toSPLNot3.L42 → D.toSPLNot3.CH_diff →
      ∀ (Fq : Type) [Field Fq] [Finite Fq] (hF : 4 ≤ Nat.card Fq), D.q = Nat.card Fq →
        SPLIsoStmt D.toSPLNot3 Fq hF

end CFSG.GH74.GLS.SP.Local
