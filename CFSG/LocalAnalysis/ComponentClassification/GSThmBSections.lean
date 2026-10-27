module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def Table517Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → h.Table517

@[expose] def Cor72Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → h.Table517 → h.Sec8Case

theorem hyp52Contradiction_of_sections (hT : Table517Statement) (hC : Cor72Statement)
    (h82 : Lemma82Statement) (h83 : Lemma83Statement) : Hyp52ContradictionStatement := by
  intro X _ _ _ hnonab hK hz hU h hmax hiso hB1 hB2a
  have hTab := hT X hnonab hK hz hU h hmax hiso hB1 hB2a
  have hcase := hC X hnonab hK hz hU h hmax hiso hB1 hB2a hTab
  exact sec8_false h82 h83 h ⟨inferInstance, hnonab, hK, hz, hU, hmax, h.smallType, hiso, hB1,
    hB2a, hcase⟩

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor) in
theorem gilman_solomon_theorem_B_iso_of_sections
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hCTI : LayerGeneratedUniversalComponentStandard) (hRS : RestrictedStandardInput)
    (hT : Table517Statement) (hC : Cor72Statement) (h82 : Lemma82Statement)
    (h83 : Lemma83Statement) : TheoremBIsoInput :=
  gilman_solomon_theorem_B_iso_of_inputs hS hU hheld hCTI hRS
    (hyp52Contradiction_of_sections hT hC h82 h83)

end CFSG.ComponentClassification.GSThmB
