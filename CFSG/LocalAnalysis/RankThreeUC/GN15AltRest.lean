module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltUniform
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBlockLift

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

theorem altEven_of_layer_and_baum (hlayer : GNLayerHolds) (hM2 : GNBaumNormalizes) :
    GNInputRed.AltEven :=
  altEven_of_inputs hlayer hM2 gnBlockLift_holds

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

