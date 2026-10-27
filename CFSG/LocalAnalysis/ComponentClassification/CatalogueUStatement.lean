module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.ComponentClassification.CatalogueU

open CFSG.Blueprint

@[expose] def CatalogAlmostSimpleUnbalancedOutcome : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    Catalog (GeneralizedFitting.subgroup X) →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (Subgroup.centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

end CFSG.ComponentClassification.CatalogueU
