module

import CFSG.LocalAnalysis.SectionRank.QTK.A134Final
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerCases
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerPair
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerJ3
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.Quasithin.Background.A129One
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.A3Structure36Base

public section

namespace CFSG.SectionRank.QTK.CentreFact

section

theorem a134Fact_holds
    : CFSG.Quasithin.A134Fact :=
  a134Fact_of_layerPair (CentreFact.layerPairFull_of_short layerPairFact_holds layerPairJ3_holds)

end

section

theorem a38Facts_holds
    : CFSG.Quasithin.A38Facts :=
  ⟨a134Fact_holds, CFSG.Quasithin.mult2Fact⟩

end

section

theorem a36Facts_holds
    : CFSG.Quasithin.A36Facts :=
  CFSG.Quasithin.A36Facts.of_proved CFSG.Quasithin.a129One CFSG.Quasithin.l2MultiplierFact
    CFSG.QuasithinUnique.Vol2Native.threeCoverFactCat CFSG.Quasithin.a23SQTKListFact
    CFSG.Quasithin.catalogStepFact

end

end CFSG.SectionRank.QTK.CentreFact
