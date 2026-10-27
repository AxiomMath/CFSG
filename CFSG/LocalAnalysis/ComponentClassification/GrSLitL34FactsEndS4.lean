module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicEight
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOutSquare

public section

namespace CFSG.ComponentClassification.GrSLit

theorem l34CyclicCentralEightFact :
    L34CyclicCentralEightFact :=
  L34Facts.cyclicCentralEight

theorem l34EightTransvectionFact :
    L34EightTransvectionFact :=
  L34Facts.eightTransvection

theorem l34OutSquareFact :
    L34OutSquareFact :=
  L34Facts.outSquare

end CFSG.ComponentClassification.GrSLit
