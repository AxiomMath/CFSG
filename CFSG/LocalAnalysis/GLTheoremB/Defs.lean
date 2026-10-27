module

public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsPPlane (p : ℕ) (D : Subgroup G) : Prop :=
  IsElemAbelian p D ∧ Nat.card D = p ^ 2

@[expose] def IsNoncyclicElemAbelianIn (p : ℕ) (X E : Subgroup G) : Prop :=
  E ≤ X ∧ IsElemAbelian p E ∧ ¬ IsCyclic E

@[expose] def IsConnectingStep (p : ℕ) (X A B : Subgroup G) : Prop :=
  IsNoncyclicElemAbelianIn p X A ∧ IsNoncyclicElemAbelianIn p X B ∧
    A ≤ Subgroup.centralizer (B : Set G)

@[expose] def IsTwoConnectedIn (p : ℕ) (X E E' : Subgroup G) : Prop :=
  IsNoncyclicElemAbelianIn p X E ∧ IsNoncyclicElemAbelianIn p X E' ∧
    Relation.ReflTransGen (IsConnectingStep p X) E E'

@[expose] def IsBOneMax [Finite G] (p : ℕ) (B : Subgroup G) : Prop :=
  GLAIsBmax p B ∧ ∃ D : Subgroup G, D ≤ B ∧ IsPPlane p D ∧ Even (Nat.card (GLADelta p D))

@[expose] def IsBZeroMax [Finite G] (p : ℕ) (B : Subgroup G) : Prop :=
  GLAIsBmax p B ∧ ∃ D : Subgroup G, D ≤ B ∧ IsPPlane p D ∧
    ((3 < p → Even (Nat.card (GLADelta p D))) ∧
      (p = 3 → Even (Nat.card (⁅GLADelta p D, B⁆ : Subgroup G))))

@[expose] def IsStronglyLocallyOneBalanced (p : ℕ) (B : Subgroup G) (b : G) (L : Subgroup G) :
    Prop :=
  ∀ S : Subgroup G, S ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G) →
    Nat.Coprime p (Nat.card S) →
    B ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (S : Set G) →
      ⁅L, S⁆ ≤ GLAPPrimeCoreOf p L

@[expose] noncomputable def lambdaOf (p : ℕ) (B : Subgroup G) (b : G) : Subgroup G :=
  sSup {L | GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L ∧
    ¬ IsStronglyLocallyOneBalanced p B b L}

@[expose] noncomputable def lambdaStar (p : ℕ) (B : Subgroup G) (b : G) : Subgroup G :=
  lambdaOf p B b ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) ⊔
    GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set G))

@[expose] noncomputable def lambdaStarGroup (p : ℕ) (B : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), lambdaStar p B b

end CFSG.LocalAnalysis.GLTheoremB
