module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Inputs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs

public section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit

@[expose] def L34FieldUnitaryExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (b y v : X) (K : Subgroup X), GSUnbalancingTriple b y K → b ∈ K →
      IsL34Type (K ⧸ Open.fusionZStar K) → Nat.card (zStarIn K) = 16 * Nat.card (oddIn K) →
      IsL34Unitary K y → v * b = b * v → v * y = y * v → HarrisLit.EndB.IsL34Field K v → False

end CFSG.ComponentClassification.TBLit
