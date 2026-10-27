module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBShell

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CorollaryCStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X → CorollaryCConclusion X

end CFSG.ComponentClassification.GSThmB
