module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

structure Hyp62 {G : Type} [Group G] (z : G) (M N A B : Subgroup G) (r : ℕ) : Prop where
  maximal : IsCoatom N
  z_mem : z ∈ N
  prime : r.Prime
  A_le : A ≤ N
  B_le : B ≤ N
  A_comm : ⁅A, zpowers z⁆ = A
  A_le_Or : A ≤ Op r M
  A_mem : NF z M A
  B_le_E : B ≤ pPrimeCoreOf r (Fm M)
  B_mem : NF z M B

@[expose] def Prop6_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ X : Subgroup G, X ≤ Op p M → X ≠ ⊥ → Cen z ≤ normalizer (X : Set G) → NF z M X

@[expose] def Lemma6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ (N A B : Subgroup G) (r : ℕ), Hyp62 z M N A B r → Fm N ≤ M

@[expose] def Lemma6_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ (N A B : Subgroup G) (r : ℕ), Hyp62 z M N A B r → Fs N ≤ M

@[expose] def Prop6_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ (N A B : Subgroup G) (r : ℕ), Hyp62 z M N A B r →
      (Fs N ≤ M ∧ Links N M) ∧ TwoPrimes (Fm N) ∧ (Links M N → M = N)

@[expose] def Prop6_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ (A : Subgroup G) (r : ℕ), r.Prime → ⁅A, zpowers z⁆ = A → A ≤ Op r M → NF z M A →
      ∀ X : Subgroup G, X ≤ pPrimeCoreOf r (Fm M) → X ≠ ⊥ → z ∈ normalizer (X : Set G) → NF z M X

@[expose] def Prop6_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ X : Subgroup G, X ≤ Ep p M → X ≠ ⊥ → z ∈ normalizer (X : Set G) → NF z M X

@[expose] def Prop6_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ (r : ℕ) (V : Subgroup G), r.Prime → V ≤ Op r M ⊓ Cen z → IsElementaryAbelian r ↥V → Nat.card ↥V = r ^ 2 →
      (∀ v ∈ V, v ≠ 1 → NF z M (zpowers v)) →
      ∀ X : Subgroup G, X ≤ Fm M → X ≠ ⊥ → V ⊔ zpowers z ≤ normalizer (X : Set G) → NF z M X

@[expose] def Prop6_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    (∀ X : Subgroup G, X ≤ Fm M → X ≠ ⊥ → z ∈ normalizer (X : Set G) → NF z M X) ∨
      (IsCyclic ↥(Ep p M) ∧ Ep p M ≤ Cen z)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
