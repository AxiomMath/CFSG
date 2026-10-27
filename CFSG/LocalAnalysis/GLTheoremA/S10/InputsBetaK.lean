module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

section FG

variable {G : Type} [Group G] [Finite G]

@[expose] def GFOn (p : ℕ) (g : G) (L : Subgroup G) : Prop :=
  NonInnDiag p g L ∧ ¬ (p = 3 ∧ IsTD4 3 L) ∧ centCard2 p L g ^ p = card2 p L

@[expose] def FGOn (p : ℕ) (g : G) (L : Subgroup G) : Prop := FieldOn p g L ∨ GFOn p g L

end FG

end S10

@[expose] def I158Base {G : Type} [Group G] [Finite G] (p : ℕ) (X K B : Subgroup G) (x₁ x₂ : G)
    (L₁ L₂ : Subgroup G) : Prop :=
  CFSG.Open.IsKGroup ↥X ∧ GLAPComponent p X K ∧ IsElemAbelian p B ∧ B ≤ X ∧
    p ^ GLATwoLocalRank p ↥X ≤ Nat.card B ∧ x₁ ∈ B ∧ x₂ ∈ B ∧ x₁ ≠ 1 ∧ x₂ ≠ 1 ∧
    GLAPComponent p (K ⊓ Subgroup.centralizer ({x₁} : Set G)) L₁ ∧ IsChevSimple 2 (PSimple p L₁) ∧
    GLAPComponent p (K ⊓ Subgroup.centralizer ({x₂} : Set G)) L₂ ∧ IsChevSimple 2 (PSimple p L₂)

@[expose] def I158HypK {G : Type} [Group G] [Finite G] (p : ℕ) (X K B : Subgroup G) (x₁ x₂ : G)
    (L₁ L₂ : Subgroup G) : Prop :=
  I158Base p X K B x₁ x₂ L₁ L₂ ∧ FGOn p x₁ L₂ ∧ FGOn p x₂ L₁

@[expose] def I158FGUp (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K : Subgroup G) (x y : G) (J : Subgroup G),
    GLAPComponent p X K → IsChevSimple 2 (PSimple p K) →
    x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ∉ Subgroup.zpowers y → y ∉ Subgroup.zpowers x →
    InnDiagOn p (Subgroup.zpowers x) K → FieldOn p y K →
    GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set G)) J → y ∈ Subgroup.normalizer (J : Set G) →
    FGOn p y J

structure I158AtK (G : Type) [Group G] [Finite G] : Prop where
  inn : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G) (x₁ x₂ : G) (L₁ L₂ : Subgroup G),
    I158Base p X K B x₁ x₂ L₁ L₂ → FieldOn p x₁ L₂ → FieldOn p x₂ L₁ →
    catalogIs (PSimple p L₁) S9.isU3eight → catalogIs (PSimple p L₂) S9.isU3eight →
    InnDiagOn p (Subgroup.zpowers x₁) K ∧ InnDiagOn p (Subgroup.zpowers x₂) K
  main : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G) (x₁ x₂ : G) (L₁ L₂ : Subgroup G),
    I158HypK p X K B x₁ x₂ L₁ L₂ → GLAPLayer p (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) ≠ ⊥ →
    p = 3 ∧ ∃ n : ℕ, Odd n ∧ 1 < n ∧
      ((catalogIs (PSimple 3 K) (S10.isU6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isL2n (3 * n)) ∧
          (∃ M : Subgroup G, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) M ∧
            catalogIs (PSimple 3 M) (S10.isL2n n)) ∧
          Nat.card B = 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K)) ∨
        (catalogIs (PSimple 3 K) (S10.isTE6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isU3n (3 * n)) ∧
          (∃ M : Subgroup G, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) M ∧
            catalogIs (PSimple 3 M) (S10.isU3n n)) ∧
          Nat.card B = 3 ^ 4 * Nat.card ↥(B ⊓ centModSubgroup 3 K))) ∧
      ∀ T : Subgroup G, T ≤ X → IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥
  fg : I158FGUp G

end CFSG.LocalAnalysis.GLTheoremA

end
