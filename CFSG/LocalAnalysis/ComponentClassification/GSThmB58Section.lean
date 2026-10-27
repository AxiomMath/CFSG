module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBIsoAt
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def NoFusionStatement58 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J →
      ∀ y : X, h.SecCond y →
      Seven.IsSylowIn (h.S ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y) →
      ∀ g : X, g ∈ h.secG0 y →
        g ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) →
        g ∈ normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X) → IsPGroup 2 (zpowers g) →
        g * h.a * g⁻¹ * h.a⁻¹ ∈ h.secB0 y → g * h.a = h.a * g

end CFSG.ComponentClassification.GSThmB
