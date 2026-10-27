module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBIsoAt

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {H : Type} [Group H] [Finite H]

@[expose] def NoFusionW (h : Hyp52 H) : Prop :=
  ∀ w ∈ normalizer (h.B : Set H), w ∈ normalizer (h.Q : Set H) →
    ∀ R : Subgroup H, IsPGroup 2 R → w ∈ R → h.a ∈ R →
      ∀ β ∈ h.B, w * h.a * w⁻¹ = β * h.a → w * h.a = h.a * w

end Hyp52

@[expose] def NF58Setting (X : Type) [Group X] [Finite X] (h : Hyp52 X) : Prop :=
  IsSimpleGroup X ∧ (∃ u v : X, u * v ≠ v * u) ∧ Assembly.KProper Blueprint.Catalog X ∧
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) ∧
    ¬ OutcomeLocal.UOutcome X ∧ GSMaximalUnbalancingTriple h.a h.x h.J ∧ GSIsoAt h.a h.J ∧
    ¬ ConclusionB1 h.J ∧ ¬ ConclusionB2a h.a h.J

end CFSG.ComponentClassification.GSThmB
