module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma515
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBIsoAt
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def SectionStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → h.SectionData

@[expose] def Elim516Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → ¬ h.Row516

theorem table517_of_inputs (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCFi : CFProp23IndexElim)
    (hSol : SolomonTwoSubgroupAltInput) (hHS : HarrisSolomonA7Input) (hST : SuzukiTausskyInput)
    (hHe : CFHeNoA5) (hP23 : CFProp23L34) (hRank : CFL34CoverRank) (hOut : CFL34CoverOut)
    (hAut : CFAutL2Rank) (hP21 : CFProp21A10) (hLoc : CFA10Local) (hNO : CFA10NoOuter)
    (hsec : SectionStatement) (h16 : Elim516Statement) :
    ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
      Assembly.KProper Blueprint.Catalog X →
      (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
      ¬ OutcomeLocal.UOutcome X →
      ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
        GSIsoAt h.a h.J →
        ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → h.Table517 := by
  intro X _ _ _ hnonab hKP hz hU h hmax hbd hnB1 hnB2a
  have hB5 := genFittingSimpleStatement
  have hB6 := sylowKernelStatement
  have hB7 := embedsTQuotStatement
  exact h.table517_of_rows hB1 hB6 hCF23 hCF24
    (h.elim513 hnonab hKP hz hU hB1 hCF23 hCFi hB5 hB6 hB7 hSol hHS hHe
      (hsec X hnonab hKP hz hU h hmax hbd hnB1 hnB2a))
    (h.not_row514 hB1 hB6 hB7 hCF23 hCF24 hCFc hCFi hST hP23 hRank hOut hAut
      (hsec X hnonab hKP hz hU h hmax hbd hnB1 hnB2a))
    (h.not_row515 hB1 hB6 hB7 hCF23 hCF24 hCFc hP21 hLoc hNO
      (hsec X hnonab hKP hz hU h hmax hbd hnB1 hnB2a))
    (h16 X hnonab hKP hz hU h hmax hbd hnB1 hnB2a)

end CFSG.ComponentClassification.GSThmB
