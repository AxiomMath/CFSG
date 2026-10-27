module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Lemma9_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (p : ℕ), p.Prime → ∀ (N X : Subgroup G), IsCoatom N → IsPGroup p ↥X →
    X ≠ ⊥ → z ∈ normalizer (X : Set G) → normalizer (X : Set G) ≤ N → ¬ NN z p ⊤ X → Fs N ≠ Op p N

@[expose] def Lemma9_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ (N X Y : Subgroup G), IsCoatom N → normalizer (X : Set G) ≤ N → Y ≤ N → NN z p ⊤ Y →
      IsPGroup p ↥(X ⊔ Y) →
      pPrimeCoreOf p N ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G) = ⊥ ∧
      Em (N ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G)) = ⊥

@[expose] def Prop9_27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ (N X : Subgroup G), IsCoatom N → NN z p (Op p M) X → X ≤ N → X ≤ Op p N → Fs N = Op p N

@[expose] def Lemma9_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ Q : Subgroup G, QP z p (Op p M) Q →
      (∀ X : Subgroup G, X ≤ Q → X ≠ ⊥ → z ∈ normalizer (X : Set G) → NN z p (Op p M) X) ∨
      ((IsExtraspecialPGroup p ↥Q ∧ Nat.card ↥Q = p ^ 3) ∧
        (Op p M = Q ⊔ zOf (Op p M) ∧ IsCyclic ↥(zOf (Op p M)) ∧ zOf (Op p M) ≤ Cen z) ∧
        (∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → Op p M ⊓ centralizer (U : Set G) = ⊥) ∧
        CFSG.pRank 2 ↥S = 2)

@[expose] def Prop9_14c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ Q : Subgroup G, QP z p (Op p M) Q →
      ∀ X : Subgroup G, X ≤ Q → X ≠ ⊥ → z ∈ normalizer (X : Set G) → NN z p (Op p M) X

end CFSG.GH74.GLS.Stage2.Bender.Thm2
