module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134Defs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerDefs
import CFSG.LocalAnalysis.SectionRank.QTK.A134Of
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListOf
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerT

public section

namespace CFSG.SectionRank.QTK

theorem a134Fact_of_layerCentreOne
    (hL : QTLayerCentreFactOne) : CFSG.Quasithin.A134Fact :=
  a134Fact_of' hL qtA134List

theorem a134Fact_of_layerPair
    (hP : CentreFact.LayerPairFull) : CFSG.Quasithin.A134Fact :=
  a134Fact_of_layerCentreOne (CentreFact.qtLayerCentreFactOne_of_pair hP)

end CFSG.SectionRank.QTK
