module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiCatHolds
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmbMain

public section

namespace CFSG.SeitzReduction.RankOne

theorem u3C1GmgIdentGoldInput_of_sl2
    (hSL2 : GmiCatSL2CoverInput) : U3C1GmgIdentGoldInput :=
  u3C1GmgIdentGoldInput_holds gmiCatFourInput_holds gmiCatSimpleInput_holds
    (gmiCatSchurInput_of_sl2 hSL2)

theorem u3C1GmsLayerInput_of_top
    (hTop : CFSG.Goldschmidt.TopStatement) (hSL2 : GmiCatSL2CoverInput) : U3C1GmsLayerInput :=
  u3C1GmsLayerInput_of_gold hTop psl2BorelInput_holds (u3C1GmgIdentGoldInput_of_sl2 hSL2)

end CFSG.SeitzReduction.RankOne
