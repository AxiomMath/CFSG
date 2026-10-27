module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.Stage4.HexSL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
open scoped Pointwise commutatorElement

structure Ch6Notation (G : Type) [Group G] where
  p : ℕ
  q₁ : ℕ
  q₂ : ℕ
  z : G
  S : Subgroup G
  K₁ : Subgroup G
  K₂ : Subgroup G
  F : Subgroup G
  P₀ : Subgroup G
  H : Subgroup G
  P : Subgroup G
  X₁ : Subgroup G
  X₁' : Subgroup G
  X₂ : Subgroup G
  X₂' : Subgroup G
  w₁ : G
  w₂ : G
  a : G

variable {G : Type} [Group G]

@[expose] def HEquiv (H A B : Subgroup G) : Prop :=
  ∃ φ : ↥A ≃* ↥B, ∀ h ∈ H, ∀ (x : ↥A) (hx : h * (x : G) * h⁻¹ ∈ A),
    ((φ ⟨h * (x : G) * h⁻¹, hx⟩ : ↥B) : G) = h * ((φ x : ↥B) : G) * h⁻¹

@[expose] def Ch6Notation.root (D : Ch6Notation G) (i : ℤ) : Subgroup G :=
  if i = 1 then D.X₁ else if i = 2 then conjBy (D.a ^ 2) D.X₂' else
  if i = 3 then conjBy D.a D.X₁' else if i = 4 then D.X₂ else
  if i = 5 then conjBy (D.a ^ 2) D.X₁ else if i = 6 then conjBy D.a D.X₂' else
  if i = -1 then D.X₁' else if i = -2 then conjBy (D.a ^ 2) D.X₂ else
  if i = -3 then conjBy D.a D.X₁ else if i = -4 then D.X₂' else
  if i = -5 then conjBy (D.a ^ 2) D.X₁' else if i = -6 then conjBy D.a D.X₂ else ⊥

@[expose] def Ch6Notation.r₂ (D : Ch6Notation G) : G := D.a⁻¹ * D.w₂ * D.a

@[expose] def Ch6Notation.N (D : Ch6Notation G) : Subgroup G :=
  Subgroup.closure ((D.H : Set G) ∪ {D.w₁, D.r₂})

structure Ch6Basics (D : Ch6Notation G) : Prop where
  prime : D.p.Prime
  p_ne_two : D.p ≠ 2
  q₁_pow : ∃ m : ℕ, D.q₁ = D.p ^ m
  q₂_pow : ∃ n : ℕ, D.q₂ = D.p ^ n
  q₁_odd : Odd D.q₁
  q₂_odd : Odd D.q₂
  q₁_ge : 5 ≤ D.q₁
  q₂_ge : 3 ≤ D.q₂
  q_rel : D.q₁ = D.q₂ ∨ D.q₁ = D.q₂ ^ 3
  z_ord : orderOf D.z = 2
  one_class : ∀ u : G, orderOf u = 2 → IsConj D.z u
  O2prime : pPrimeCore 2 ↥(centralizer ({D.z} : Set G)) = ⊥
  K₁_eq : D.K₁ = D.X₁ ⊔ D.X₁'
  K₂_eq : D.K₂ = D.X₂ ⊔ D.X₂'
  K_comm : ∀ x ∈ D.K₁, ∀ y ∈ D.K₂, x * y = y * x
  iso₁ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = D.q₁ ∧ Nonempty (↥D.K₁ ≃* SL2 F)
  iso₂ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = D.q₂ ∧ Nonempty (↥D.K₂ ≃* SL2 F)
  z_mem_K₁ : D.z ∈ D.K₁
  z_mem_K₂ : D.z ∈ D.K₂
  card_X₁ : Nat.card ↥D.X₁ = D.q₁
  card_X₁' : Nat.card ↥D.X₁' = D.q₁
  card_X₂ : Nat.card ↥D.X₂ = D.q₂
  card_X₂' : Nat.card ↥D.X₂' = D.q₂
  X₁_comm : ∀ x ∈ D.X₁, ∀ y ∈ D.X₁, x * y = y * x
  X₁'_comm : ∀ x ∈ D.X₁', ∀ y ∈ D.X₁', x * y = y * x
  X₂_comm : ∀ x ∈ D.X₂, ∀ y ∈ D.X₂, x * y = y * x
  X₂'_comm : ∀ x ∈ D.X₂', ∀ y ∈ D.X₂', x * y = y * x
  X₁_exp : ∀ x ∈ D.X₁, x ^ D.p = 1
  X₁'_exp : ∀ x ∈ D.X₁', x ^ D.p = 1
  X₂_exp : ∀ x ∈ D.X₂, x ^ D.p = 1
  X₂'_exp : ∀ x ∈ D.X₂', x ^ D.p = 1
  X₁_ne : D.X₁ ≠ D.X₁'
  X₂_ne : D.X₂ ≠ D.X₂'
  H_comm : ∀ x ∈ D.H, ∀ y ∈ D.H, x * y = y * x
  H_pPrime : ∀ h ∈ D.H, ¬ D.p ∣ orderOf h
  z_mem_H : D.z ∈ D.H
  H_norm_X₁ : ∀ h ∈ D.H, ∀ x ∈ D.X₁, h * x * h⁻¹ ∈ D.X₁
  H_norm_X₁' : ∀ h ∈ D.H, ∀ x ∈ D.X₁', h * x * h⁻¹ ∈ D.X₁'
  H_norm_X₂ : ∀ h ∈ D.H, ∀ x ∈ D.X₂, h * x * h⁻¹ ∈ D.X₂
  H_norm_X₂' : ∀ h ∈ D.H, ∀ x ∈ D.X₂', h * x * h⁻¹ ∈ D.X₂'
  card_H_K₁ : Nat.card ↥(D.H ⊓ D.K₁) = D.q₁ - 1
  card_H_K₂ : Nat.card ↥(D.H ⊓ D.K₂) = D.q₂ - 1
  w₁_mem : D.w₁ ∈ D.K₁
  w₂_mem : D.w₂ ∈ D.K₂
  w₁_sq : D.w₁ * D.w₁ = D.z
  w₂_sq : D.w₂ * D.w₂ = D.z
  w₁_swap : ∀ x ∈ D.X₁, D.w₁ * x * D.w₁⁻¹ ∈ D.X₁'
  w₁_swap' : ∀ x ∈ D.X₁', D.w₁ * x * D.w₁⁻¹ ∈ D.X₁
  w₂_swap : ∀ x ∈ D.X₂, D.w₂ * x * D.w₂⁻¹ ∈ D.X₂'
  w₂_swap' : ∀ x ∈ D.X₂', D.w₂ * x * D.w₂⁻¹ ∈ D.X₂
  w₁_normH : D.w₁ ∈ normalizer (D.H : Set G)
  w₂_normH : D.w₂ ∈ normalizer (D.H : Set G)
  a_normH : D.a ∈ normalizer (D.H : Set G)
  a_cube : D.a ^ 3 ∈ D.H
  w₁_a : ∃ h ∈ D.H, D.w₁ * D.a * D.w₁⁻¹ = D.a⁻¹ * h
  w₂_a : ∃ h ∈ D.H, D.w₂ * D.a * D.w₂⁻¹ = D.a⁻¹ * h
  a_mem_N : D.a ∈ D.N
  S_pGroup : IsPGroup 2 ↥D.S
  S_sylow : ¬ 2 ∣ D.S.index
  z_mem_S : D.z ∈ D.S
  S_idx : (D.S ⊓ (D.K₁ ⊔ D.K₂)).relIndex D.S = 2
  S_le : D.S ≤ ⨆ n ∈ D.N, conjBy n (D.K₁ ⊔ D.K₂)
  F_odd : ∀ f ∈ D.F, Odd (orderOf f)
  F_normN : D.F ≤ normalizer (D.N : Set G)
  C_le : centralizer ({D.z} : Set G) ≤ D.K₁ ⊔ D.K₂ ⊔ D.S ⊔ D.F
  P₀_le : D.P₀ ≤ D.F
  P₀_pGroup : IsPGroup D.p ↥D.P₀

structure Ch6Core (D : Ch6Notation G) : Prop extends Ch6Basics D where
  P_pGroup : IsPGroup D.p ↥D.P
  P_card : Nat.card ↥D.P = D.q₁ ^ 3 * D.q₂ ^ 3
  P_normH : ∀ h ∈ D.H, ∀ x ∈ D.P, h * x * h⁻¹ ∈ D.P
  P_gen : D.P = ⨆ k ∈ Set.Icc (1 : ℤ) 6, D.root k
  opp : D.P ⊓ conjBy (D.w₁ * D.w₂) D.P = ⊥
  F_normB : D.F ≤ normalizer ((D.H ⊔ D.P : Subgroup G) : Set G)
  P₀_normP : D.P₀ ≤ normalizer (D.P : Set G)
  Sylow_PP₀ : ∃ T : Sylow D.p G, (T : Subgroup G) = D.P ⊔ D.P₀
  inequiv : ∀ i j : ℤ, 1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → i ≠ j → ¬ HEquiv D.H (D.root i) (D.root j)
  long_A2 : (∀ x ∈ D.root 2, ∀ y ∈ D.root 4, x * y = y * x) ∧
    (∀ x ∈ D.root 4, ∀ y ∈ D.root 6, x * y = y * x) ∧
    (∀ x ∈ D.root 2, ∀ y ∈ D.root 6, ⁅x, y⁆ ∈ D.root 4)

@[expose] def Ch6Notation.L92 (D : Ch6Notation G) : Prop :=
  ∀ Z : Subgroup G, Z ≤ D.P → (∀ h ∈ D.H, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z) →
    ∀ l : List ℤ, l.Nodup → (∀ i, i ∈ l ↔ IsRoot 6 i ∧ D.root i ≤ Z) →
      (Z : Set G) = chainProd D.root l ∧ Nat.card ↥Z = (l.map fun i => Nat.card ↥(D.root i)).prod

@[expose] def Ch6Notation.ZClass (D : Ch6Notation G) : Prop :=
  ∀ t ∈ D.S ⊓ (D.K₁ ⊔ D.K₂), orderOf t = 2 → ∃ g ∈ (D.H ⊔ D.P) ⊔ D.N, g * D.z * g⁻¹ = t

structure Ch6Post (D : Ch6Notation G) : Prop where
  core : Ch6Core D
  L92 : D.L92
  zclass : D.ZClass

end CFSG.GH74.GLS.Stage4.Rest
