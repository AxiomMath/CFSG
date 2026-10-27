module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

@[expose] def TwoGroupAltCoverExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (A : Subgroup X) (m : ℕ) (R : Subgroup X), A ≠ ⊥ → IsPGroup 2 A → Odd m → 9 ≤ m →
      R ≤ centralizer (A : Set X) → IsPComponent 2 (R.subgroupOf (centralizer (A : Set X))) →
      Nonempty (R ⧸ Open.fusionZStar R ≃* alternatingGroup (Fin m)) →
      Open.fusionZStar R = pPrimeCore 2 R

end CFSG.ComponentClassification.SolMax
