module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryField
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldPlaneMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftU38

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

theorem kFactSL3LiftGenUnitaryField :
    KFactSL3LiftGenFor SL3LiftUnitary.IsUnitaryFieldIndex :=
  kFactSL3LiftGenUnitaryField_of_gen
    (fun h hq₀ K₀ hK₀ => subfieldDiagGen_of_four_le h rfl hq₀ K₀ hK₀)
    (fun h K₀ hK₀ => subfieldDiagGen_eight h K₀ hK₀)

theorem kFactSL3LiftGenUnitary :
    KFactSL3LiftGenUnitary :=
  SL3LiftUnitary.kFactSL3LiftGenUnitary_of_cases SL3LiftUnitary.kFactSL3LiftGenUnitaryInner
    kFactSL3LiftGenUnitaryField

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
