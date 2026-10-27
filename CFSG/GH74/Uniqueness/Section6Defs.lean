module

public import CFSG.GH74.Uniqueness.Prop38
public import CFSG.GH74.Uniqueness.Section5Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def oPrimePrime (p : ℕ) (D : Subgroup X) : Subgroup X :=
  (pPrimeCore p ↥(pPrimeCoreIn D)).map (pPrimeCoreIn D).subtype

@[expose] noncomputable def zjSubgroup (p : ℕ) (R : Subgroup X) : Subgroup X :=
  (omega₁ (G := thompsonCenter (G := X) R) (p := p)).map
    (thompsonCenter (G := X) R).subtype

structure T4Cand (Z : Set X) (M : Subgroup X) (z : X) (p : ℕ) (W : Subgroup X) : Prop where
  mem_Z : z ∈ Z
  mem_M : z ∈ M
  prime : p.Prime
  ne_two : p ≠ 2
  pgroup : IsPGroup p W
  le_M : W ≤ M
  normalizes : z ∈ normalizer (W : Set X)
  comm_eq : ⁅zpowers z, W⁆ = W
  ne_bot : W ≠ ⊥
  two_le : 2 ≤ (omegaFix M (W : Set X)).ncard

structure T4Max (Z : Set X) (M : Subgroup X) (z : X) (p : ℕ) (W : Subgroup X) : Prop where
  cand : T4Cand Z M z p W
  max : ∀ W' : Subgroup X, T4Cand Z M z p W' →
    Nat.card (CFSG.OddInversion.invertedSet W' z) ≤ Nat.card (CFSG.OddInversion.invertedSet W z)

@[expose] def STriple (Z : Set X) (M : Subgroup X) (γ δ : Subgroup X) (s : X) : Prop :=
  γ ∈ omega M ∧ δ ∈ omega M ∧ s ∈ Z ∧ conjugate γ s = γ ∧ γ ≠ δ

@[expose] def TransitiveOnS (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ γ₁ δ₁ s₁ γ₂ δ₂ s₂, STriple Z M γ₁ δ₁ s₁ → STriple Z M γ₂ δ₂ s₂ →
    ∃ g : X, conjugate γ₁ g = γ₂ ∧ conjugate δ₁ g = δ₂ ∧ g⁻¹ * s₁ * g = s₂

@[expose] def Theorem4bStmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z ∈ Z, z ∈ M → ∀ W : Subgroup X, Odd (Nat.card W) → W ≤ M → z ∈ normalizer (W : Set X) →
    (∀ w ∈ W, z * w = w * z) ∨ ∀ β ∈ omegaFix M (W : Set X), β = M

@[expose] def Theorem4Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  DoublyTransitive M ∧ Theorem4bStmt Z M

@[expose] def Cor5bStmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ γ δ s, STriple Z M γ δ s →
    γ ⊓ δ ⊓ conjugate δ s = (γ ⊓ δ) ⊓ centralizer ({s} : Set X)

@[expose] def Cor5Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  TransitiveOnS Z M ∧ Cor5bStmt Z M

@[expose] def Lemma61aStmt (Z : Set X) (M : Subgroup X) : Prop :=
  DoublyTransitive M → TransitiveOnS Z M

@[expose] def Theorem2Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    ((∃ P : Subgroup X, IsPGroup p P ∧ (omegaFix M (P : Set X)).ncard = 2) → DoublyTransitive M) ∧
    ((¬ ∃ P : Subgroup X, IsPGroup p P ∧ (omegaFix M (P : Set X)).ncard = 2) →
      ∀ β ∈ omega M, ∀ P : Subgroup X, IsPGroup p P → P ≤ β →
        3 ≤ (omegaFix M (P : Set X)).ncard →
        (∀ Q : Subgroup X, IsPGroup p Q → Q ≤ β → 3 ≤ (omegaFix M (Q : Set X)).ncard →
          P ≤ Q → Q = P) →
        (∀ γ ∈ omegaFix M (P : Set X), ∀ δ ∈ omegaFix M (P : Set X),
          ∃ n ∈ normalizer (P : Set X), conjugate γ n = δ) ∧
        ∀ γ ∈ omegaFix M (P : Set X), ∃ s ∈ Z, s ∈ normalizer (P : Set X) ∧ conjugate γ s = γ)

@[expose] def Prop63Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Cand Z M z p W → ∀ t ∈ Z, t ∉ M → conjugate M t ∈ omegaFix M (W : Set X) →
    lSubgroup M z t = ⊤

@[expose] def Cor64Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Cand Z M z p W → ∀ β ∈ omegaFix M (W : Set X), β ≠ M →
    z ∈ normalizer (oPrimePrime p (M ⊓ β) : Set X) →
      oPrimePrime p (M ⊓ β) = ⊥ ∧
        ∀ R : Subgroup X, R ≤ M ⊓ β → IsPGroup p R →
          (∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q (pPrimeCoreIn (M ⊓ β)) ∧ Q ≤ R) →
          z ∉ normalizer (zjSubgroup p R : Set X)

@[expose] def Lemma62Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Max Z M z p W → ∀ γ ∈ omegaFix M (W : Set X), γ ≠ M →
    ((∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q (M ⊓ γ) ∧ z ∈ normalizer (Q : Set X)) ↔
      Nat.card (CFSG.OddInversion.invertedSet W z) = zNumShare Z M p)

@[expose] def Lemma73Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Max Z M z p W → ∀ β ∈ omegaFix M (W : Set X), β ≠ M →
    (∀ Q : Subgroup X, IsPGroup p Q → Q ≤ M ⊓ β ⊓ conjugate β z → z ∈ normalizer (Q : Set X) →
      ∃ P : Subgroup X, ABGLocalTools.IsSylowOf p P (M ⊓ β ⊓ conjugate β z) ∧ Q ≤ P ∧
        z ∈ normalizer (P : Set X)) ∧
    ∀ P : Subgroup X, ABGLocalTools.IsSylowOf p P (M ⊓ β ⊓ conjugate β z) →
      z ∈ normalizer (P : Set X) →
        ∃ t ∈ Z, t ∈ normalizer (P : Set X) ∧ conjugate M t = β

@[expose] def Prop72Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Max Z M z p W → ∃ β ∈ omegaFix M (W : Set X), β ≠ M ∧ oPrimePrime p (M ⊓ β) = ⊥

@[expose] def Prop78Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Max Z M z p W → DoublyTransitive M

@[expose] def Prop79Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Max Z M z p W →
    Nat.card (CFSG.OddInversion.invertedSet W z) < zNumShare Z M p

@[expose] def Prop71Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ z p W, T4Max Z M z p W → Nat.card (CFSG.OddInversion.invertedSet W z) = 1

end CFSG.GH74.Uniqueness
