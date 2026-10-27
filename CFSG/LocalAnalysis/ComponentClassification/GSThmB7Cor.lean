module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Set
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Core

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def ClassicalInvolutionStatement71 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → h.Table517 → conjugate h.K h.a ≠ h.K →
      ∀ s : Seven.Setting X, h.IsX0Min s.y → Seven.Prop62Output h s.h s.y →
      normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) →
      ∀ b : X, Seven.Lemma61Case2 s.h s.y b →
      ∃ (δ : X) (J' : Subgroup X), orderOf δ = 2 ∧ J' ≤ centralizer ({δ} : Set X) ∧
        IsPComponent 2 (J'.subgroupOf (centralizer ({δ} : Set X))) ∧ δ ∈ J' ∧
        CFSG.pRank 2 J' ≤ 1 ∧ Open.classicalInvolutionWitness J'

end CFSG.ComponentClassification.GSThmB
