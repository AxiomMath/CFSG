module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Prop9_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ X : Subgroup G, X ≤ Op p M → X ≠ ⊥ → Cen z ≤ normalizer (X : Set G) → ⁅X, zpowers z⁆ = X →
      NN z p (Op p M) X

@[expose] def Prop9_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ N A B : Subgroup G, IsCoatom N → A ≤ Op p M → B ≤ Op p M → A ≠ ⊥ → B ≠ ⊥ →
      z ∈ normalizer (A : Set G) → z ∈ normalizer (B : Set G) → ⁅A, zpowers z⁆ = A →
      NN z p (Op p M) A → normalizer (B : Set G) ≤ N → A ≤ N → Fs N = Op p N

@[expose] def Lemma9_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ Y Y₁ : Subgroup G, Y ≤ Op p M → Y ≠ ⊥ → z ∈ normalizer (Y : Set G) → ¬ NN z p (Op p M) Y →
      Y₁ ≤ Op p M ⊓ normalizer (Y : Set G) → Y₁ ≠ ⊥ → ⁅Y₁, zpowers z⁆ = Y₁ → ¬ NN z p (Op p M) Y₁

@[expose] def Prop9_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ X V N : Subgroup G, X ≤ Op p M → X ≠ ⊥ → z ∈ normalizer (X : Set G) → ⁅X, zpowers z⁆ = X →
      IsCoatom N → normalizer (X : Set G) ≤ N → V ≤ Op p M ⊓ N ⊓ Cen z → IsElementaryAbelian p ↥V →
      Nat.card ↥V = p ^ 2 → (∀ v ∈ V, v ≠ 1 → NN z p (Op p M) (zpowers v)) → Fs N = Op p N

@[expose] def Prop9_11c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ V X : Subgroup G, V ≤ Op p M ⊓ Cen z → IsElementaryAbelian p ↥V → Nat.card ↥V = p ^ 2 →
      (∀ v ∈ V, v ≠ 1 → NN z p (Op p M) (zpowers v)) → X ≤ Op p M → X ≠ ⊥ → ⁅X, zpowers z⁆ = X →
      V ⊔ zpowers z ≤ normalizer (X : Set G) → NN z p (Op p M) X

section MinBad

variable {G : Type} [Group G]

structure MinBad9 (z : G) (M : Subgroup G) (p : ℕ) (Q X : Subgroup G) : Prop where
  Q_mem : QP z p (Op p M) Q
  X_le : X ≤ Q
  X_ne : X ≠ ⊥
  X_inv : z ∈ normalizer (X : Set G)
  X_not : ¬ NN z p (Op p M) X
  minimal : ∀ Y : Subgroup G, Y ≤ Q → Y ≠ ⊥ → z ∈ normalizer (Y : Set G) → ¬ NN z p (Op p M) Y →
    Nat.card ↥X ≤ Nat.card ↥Y
  prefer : (∃ Y : Subgroup G, Y ≤ Q ∧ Y ≠ ⊥ ∧ z ∈ normalizer (Y : Set G) ∧ ¬ NN z p (Op p M) Y ∧
    Nat.card ↥Y = Nat.card ↥X ∧ ¬ Y ≤ Cen z) → ¬ X ≤ Cen z

end MinBad

end CFSG.GH74.GLS.Stage2.Bender.Thm2
