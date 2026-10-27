module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Assembly
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.D1EightTen
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Corner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs


open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry in
theorem citedBlockAltNormalizer_holds
    : CFSG.AGLEmbedding.CitedBlockAltNormalizer :=
  CFSG.AGLEmbedding.citedBlockAltNormalizer_of_sq
    (CFSG.HardMathSupport.RichardWeiss.Coordinator.citedBlockAltNormalizerSq_of_eightTen
      (CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.asc81bEightTen_of_E0_hyc
        (e0NonShortNotHYcStatement_of_caseI E0Sub.e0NonShortNotCaseIStatement_holds)))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
