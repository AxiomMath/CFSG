module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs56X
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs510C
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsNoFrob
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsNonElem
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowLift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsGraphInvCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Outer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Sylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Unit

public section

namespace CFSG.ComponentClassification.GrSLit

theorem l34NoFrobeniusFact :
    L34NoFrobeniusFact :=
  L34Facts.noFrobenius

theorem l34GraphInvertCoverFact :
    L34GraphInvertCoverFact :=
  L34Facts.l34GraphInvertCoverFact

theorem l34SylowCentralizerFact :
    L34SylowCentralizerFact :=
  L34Facts.sylowCentralizer

theorem l34CenterRankFact :
    L34CenterRankFact :=
  L34Facts.centerRank

theorem l34CenterNoncyclicFact :
    L34CenterNoncyclicFact :=
  L34Facts.centerNoncyclic

theorem l34ElementaryCenterSylowFact :
    L34ElementaryCenterSylowFact :=
  L34Facts.elementaryCenterSylow

theorem l34UnitaryCenterFact :
    L34UnitaryCenterFact :=
  L34Facts.unitaryCenter

theorem l34MaxElementaryThreeFact :
    L34MaxElementaryThreeFact :=
  L34Facts.maxElementaryThree

theorem l34ElementaryRankFact :
    L34ElementaryRankFact :=
  L34Facts.elementaryRank

theorem l34CommutatorFourGroupFact :
    L34CommutatorFourGroupFact :=
  L34Facts.commutatorFourGroup

theorem l34OuterInvolutionCentralizerFact :
    L34OuterInvolutionCentralizerFact :=
  L34Facts.outerInvolutionCentralizer

theorem l34SylowCentralLiftFact :
    L34SylowCentralLiftFact :=
  L34Facts.sylowCentralLift

theorem l34NonelementaryCenterCommutatorFact :
    L34NonelementaryCenterCommutatorFact :=
  L34Facts.nonelementaryCenterCommutator

end CFSG.ComponentClassification.GrSLit
