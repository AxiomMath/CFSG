module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4RIdx
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4OutInvR
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4OutInv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndT3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndS2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndS4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4SylowCtr
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGInvMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEndS4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsDischarges
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbal

public section

namespace CFSG.ComponentClassification.GrSLit

theorem l34EndTStep_of_covers
    (hExp : L34BFixExponentFact) (hSq : L34BFixOuterSquareFact) : L34EndTStep :=
  l34EndTStep_of_inputs (l34EndTShapeStep_of_covers hExp hSq) l34EightTransvectionFact

theorem l34EndFusionStep_of_covers
    (hCos : L34OuterCentralizerCosetFact) (hFix : L34OuterFixedInvolutionFact)
    (hComm : L34OuterCommutatorFact) : L34EndFusionStep :=
  l34EndFusionStep_of_invStep (l34OuterInvolutionCenterInvStep_of_facts hCos hFix hComm)
    l34OutSquareFact

theorem l34EndSylowStep_of_covers
    (hMax : MaximalTwoComponentInput)
    (hSol : SolomonFixedLayerStep) (hCube : FourCubeSylowFact) (hExp : L34BFixExponentFact)
    (hSq : L34BFixOuterSquareFact) (hCos : L34OuterCentralizerCosetFact)
    (hFix : L34OuterFixedInvolutionFact) (hComm : L34OuterCommutatorFact) :
    L34EndSylowStep :=
  have hGraph : L34EndGraphStep := FinalG.l34EndGraphStep_of_covers l34GraphInvertCoverFact hSol
    l34OutSquareFact l34NoFrobeniusFact l34EightTransvectionFact
  have hRest : L34EndStructureRestStep := l34EndStructureRestStep_of_facts
    (l34CyclicInvolutionClassFact_of_facts l34CyclicCentralEightFact l34EightTransvectionFact) l34CyclicCentralEightFact l34EightTransvectionFact
    l34OutSquareFact (l34EndTStep_of_covers hExp hSq) hGraph
  have hStr : L34EndStructureStep :=
    l34EndStructureStep_of_inputs (l34EndFusionStep_of_covers hCos hFix hComm) hRest
  l34EndSylowStep_of_inputs hMax L34Facts.l34UnbalancingUnitaryStep
    L34Facts.l34UnitaryCentralizerFact l34SylowCenterCyclicFact l34SylowCentralizerFact
    (l34EndTypeStep_of_inputs hStr hCube)

end CFSG.ComponentClassification.GrSLit
