module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Setup7

variable {G : Type} [Group G] [Finite G]

@[expose] def CaseC (z : G) (S : Subgroup G) : Prop :=
  ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (x : G),
    Stage1Pair G z S q L₁ L₂ ∧ TwoClassData G z S L₁ L₂ q x

structure V7 (z : G) (S V : Subgroup G) : Prop where
  le_S : V ≤ S
  le_L : V ≤ LC z
  four : IVK.IsFourSubgroup V
  three : 3 ∣ AutOrd (Cen z) V
  conj : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ c ∈ Cen z, c * v * c⁻¹ = w
  caseC : CaseC z S → (∀ v ∈ V, orderOf v = 2 → ¬ IsConj z v) ∧
    ∃ z' ∈ S, IsConj z z' ∧ z' ≠ z ∧ ∀ v ∈ V, z' * v = v * z'

end Setup7

@[expose] def V7_exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∃ V : Subgroup G, V7 z S V

@[expose] def Lemma7_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q V : Subgroup G, QP z p (Op p M) Q → V7 z S V →
      ∀ v ∈ V, v ≠ 1 → centralizer ({v} : Set G) ≤ M

@[expose] def Lemma7_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ V : Subgroup G, IVK.IsFourSubgroup V → (∀ v ∈ V, v ≠ 1 → centralizer ({v} : Set G) ≤ M) →
      ∀ g : G, V ≤ conjugate M g → g ∈ M

@[expose] def Lemma7_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q V : Subgroup G, QP z p (Op p M) Q → V7 z S V →
      ∀ v ∈ V, orderOf v = 2 → ¬ IsConj z v

@[expose] def Lemma7_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q V : Subgroup G, QP z p (Op p M) Q → V7 z S V → k = Kind.m12

@[expose] def Prop7_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx6 G z k S M p →
    ∀ Q : Subgroup G, QP z p (Op p M) Q → pRank 2 ↥S = 2

end CFSG.GH74.GLS.Stage2.Bender.Thm1
