module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cat82
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsDischarges
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOddFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma56R
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL2Outer
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Facts
public import CFSG.LocalAnalysis.ComponentClassification.KProperComponentLocalBOpen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKu58
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuOrbit

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma58_closed_ku
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hMax : MaximalTwoComponentInput) (hInvt : L34Sec5ComponentInvariantStep)
    (hKu : GrS5S.L34Sec5KuOddStep) :
    L34Lemma58 := by
  have hHeldInput' := KProperRelativeB.heldInput
  have hSolomonCommutingCoreInput' := solomonCommutingCoreInput
  have hGorensteinWalterConnectedInput' := gorensteinWalterConnectedInput
  have hInvolutionCentralizerFact' := L34Facts.l34InvolutionCentralizerFact
  have hL2UnbalancingSylowFact' := CatFactsL4U4.l2UnbalancingSylowFact
  have hUnbalancingUnitaryStep' := L34Facts.l34UnbalancingUnitaryStep
  have hUnitaryCentralizerFact' := L34Facts.l34UnitaryCentralizerFact
  have hCenterRankFact' := l34CenterRankFact
  have hCommutatorFourGroupFact' := l34CommutatorFourGroupFact
  have hOuterInvolutionCentralizerFact' := l34OuterInvolutionCentralizerFact
  have hLemma56' := l34Lemma56_of_facts hS hU hHeldInput' hSolomonCommutingCoreInput'
    hGorensteinWalterConnectedInput' hMax hInvolutionCentralizerFact' hL2UnbalancingSylowFact'
    hUnbalancingUnitaryStep' hUnitaryCentralizerFact' hCenterRankFact' hCommutatorFourGroupFact'
    hOuterInvolutionCentralizerFact'
  have hAutRankOneNormalFact' := HSFLit.AutL34.l34AutRankOneNormalFact
  have hUnbalancingFourFact' := L34Facts.l34UnbalancingFourFact
  have hL2UnbalancingAutFact' := HSFLit.AutL2.l2UnbalancingAutFact
  have hL2UnbalancingOuterFact' := HSFLit.AutL2.l2UnbalancingOuter
  have hLemma58OrbitStep' := l34Lemma58OrbitStep_of_inputs_ku hS hU hHeldInput'
    hSolomonCommutingCoreInput' hGorensteinWalterConnectedInput' hMax hInvolutionCentralizerFact'
    hKu hUnbalancingFourFact' hL2UnbalancingAutFact'
    hL2UnbalancingOuterFact'
  have hElementaryCenterSylowFact' := l34ElementaryCenterSylowFact
  have hNonelementaryCenterCommutatorFact' := l34NonelementaryCenterCommutatorFact
  have hUnitaryAutFact' := HSFLit.AutL34.l34UnitaryAutFact
  exact l34Lemma58_of_inputs_ku hS hU hHeldInput' hSolomonCommutingCoreInput'
    hGorensteinWalterConnectedInput' hMax hInvolutionCentralizerFact' hLemma56'
    hAutRankOneNormalFact' hKu hUnbalancingFourFact'
    hLemma58OrbitStep' hElementaryCenterSylowFact' hNonelementaryCenterCommutatorFact'
    hL2UnbalancingAutFact' hUnbalancingUnitaryStep' hUnitaryAutFact' hInvt

end CFSG.ComponentClassification.GrSLit.GrS5
