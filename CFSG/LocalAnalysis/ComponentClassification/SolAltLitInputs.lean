module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced

public section

namespace CFSG.ComponentClassification.SolAltLit

open CFSG Subgroup

@[expose] def IsAltTwoComponent {X : Type*} [Group X] (t : X) (K : Subgroup X) (n : ℕ) : Prop :=
  orderOf t = 2 ∧ K ≤ centralizer ({t} : Set X) ∧
    IsPComponent 2 (K.subgroupOf (centralizer ({t} : Set X))) ∧
    Nonempty (K ⧸ pPrimeCore 2 K ≃* alternatingGroup (Fin n))

@[expose] def AlternatingStandardFormInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ∀ (L : Subgroup G) (n : ℕ), IsStandardSubgroup L →
      8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      Nonempty (G ≃* alternatingGroup (Fin (n + 4)))

@[expose] def StandardReductionOddInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (K : Subgroup X) (n : ℕ), IsAltTwoComponent t K n → Odd n → 9 ≤ n →
      (∀ (t' : X) (K' : Subgroup X) (n' : ℕ), IsAltTwoComponent t' K' n' → Odd n' → n' ≤ n) →
      ∃ L : Subgroup X, IsStandardSubgroup L ∧ Nonempty (L ≃* alternatingGroup (Fin n))

@[expose] def StandardReductionEvenInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    (∀ (t' : X) (K' : Subgroup X) (n' : ℕ), IsAltTwoComponent t' K' n' → Odd n' → n' < 9) →
    ∀ (t : X) (K : Subgroup X) (n : ℕ), IsAltTwoComponent t K n → Even n → 8 ≤ n →
      (∀ (t' : X) (K' : Subgroup X) (n' : ℕ), IsAltTwoComponent t' K' n' → n' ≤ n) →
      ∃ L : Subgroup X, IsStandardSubgroup L ∧ Nonempty (L ≃* alternatingGroup (Fin n))

end CFSG.ComponentClassification.SolAltLit
