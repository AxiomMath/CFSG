module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.Det
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Reduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FFGlaubermanNiles

public section

namespace CFSG.Quasithin

theorem b_1_13_holds :
    CFSG.ASVolI.B_1_13 :=
  b_1_13_of_ff B113KDet.catalogBridge_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds
    CFSG.QuasithinUnique.Bridge.asB42DichotomyNat_proved LieOver.asLieTwo_holds.1
    LieOver.asLieTwo_holds.2

end CFSG.Quasithin
