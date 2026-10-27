module

public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.D1FrontierOrth
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NoIrrFF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusFinal
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClHYc

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator


theorem asc81bNineThreeNat_of_three (hTE6 : CoopersteinNoIrrFFTwistedE6)
    (hCm : LieInput.OrthMinusCentOb) (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    CFSG.RankThree.PartTwo.Sec19.Asc81bNineThreeNat :=
  Meierfrankenfeld.Coordinator.asc81bNineThreeNat_of_frontier_orth CurtisE6.coopersteinNoIrrFFE6 hTE6
    LieInput.orthPlusLeviOb LieInput.orthMinusLeviOb hCm
    (AlternatingGeometry.e0NonShortNotHYzStatement_of_hyc hE0)

theorem asc81bNineThree_of_three (hTE6 : CoopersteinNoIrrFFTwistedE6)
    (hCm : LieInput.OrthMinusCentOb) (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    CFSG.AGLEmbedding.Asc81bNineThree :=
  CFSG.RankThree.PartTwo.Sec19.asc81bNineThree_of_nat (asc81bNineThreeNat_of_three hTE6 hCm hE0)

end CFSG.HardMathSupport.Cooperstein.Coordinator
