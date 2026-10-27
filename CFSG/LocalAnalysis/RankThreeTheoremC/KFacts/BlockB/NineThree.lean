module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FrontierThree
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.FinalOfTypeBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBFinal
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusCent
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Corner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB


theorem asc81bNineThree_holds
    : CFSG.AGLEmbedding.Asc81bNineThree :=
  CFSG.HardMathSupport.Cooperstein.Coordinator.asc81bNineThree_of_three
    (CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.coopersteinNoIrrFFTwistedE6_of_typeBound
      fun _ hf K _ _ _ hK σ hσ =>
        CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.twTypeBoundStmt_proved hf K hK σ hσ)
    CFSG.HardMathSupport.Cooperstein.StructureLie.orthMinusCentOb_proved
    (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.e0NonShortNotHYcStatement_of_caseI
      CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.e0NonShortNotCaseIStatement_holds)

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB
