module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

@[expose] def GSIsoAt (a : X) (J : Subgroup X) : Prop :=
  ∀ y b : X, y ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
    GSUnbalancingTriple a y J → orderOf b = 2 → a * b = b * a → y * b = b * y →
    b ∈ coreActionKernel J →
    ∃ M : Subgroup X, UnbalancedGS.GSIsoCorr a J b M ∧ GSUnbalancingTriple b y M

end CFSG.ComponentClassification.GSThmB
