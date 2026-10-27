module

public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOdd
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatEven
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatAlternating
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerListRankOne
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadic

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

theorem gmsLinearStandardLayerListKRankOne :
    GMSLinearStandardLayerListKRankOneStatement :=
  gmsLinearStandardLayerListKRankOne_of_families fixedRootSelector_alternating
      fixedRootSelector_oddLieType fixedRootSelector_evenLieType
      Sporadic.fixedRootSelector_sporadicRep

end CFSG.LocalAnalysis.EvenBN.GMSK
