module

public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.D1Frontier
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.RestOrth
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusCent
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClHYz
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FrontierNodes
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.FinalSmall

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

open CFSG.HardMathSupport.Cooperstein CFSG.HardMathSupport.Cooperstein.Coordinator


theorem asc81bNineThreeNat_of_frontier_orth (hE6 : CoopersteinNoIrrFFE6)
    (hTE6 : CoopersteinNoIrrFFTwistedE6) (hLp : LieInput.OrthPlusLeviOb)
    (hLm : LieInput.OrthMinusLeviOb) (hCm : LieInput.OrthMinusCentOb)
    (hE0 : AlternatingGeometry.E0NonShortNotHYzStatement) :
    CFSG.RankThree.PartTwo.Sec19.Asc81bNineThreeNat :=
  asc81bNineThreeNat_of_nodes LieOdd.gf2NoFFLieOddSmall
    (coopersteinNoFFExceptionalRestNoE8_of_e6Families hE6 hTE6)
    (eightNineNonParabolic_of_lieInputRest
      (LieInput.lieInputRest_of_orth_nodes hLp LieInput.orthPlusCentOb hLm hCm))
    (AlternatingGeometry.eightTenNodeFourOrbit_of_E0_hyz hE0)
    (AlternatingGeometry.eightTenNodeColourFour_of_E0_hyz hE0)

theorem asc81bNineThree_of_frontier_orth (hE6 : CoopersteinNoIrrFFE6)
    (hTE6 : CoopersteinNoIrrFFTwistedE6) (hLp : LieInput.OrthPlusLeviOb)
    (hLm : LieInput.OrthMinusLeviOb) (hCm : LieInput.OrthMinusCentOb)
    (hE0 : AlternatingGeometry.E0NonShortNotHYzStatement) :
    CFSG.AGLEmbedding.Asc81bNineThree :=
  CFSG.RankThree.PartTwo.Sec19.asc81bNineThree_of_nat
    (asc81bNineThreeNat_of_frontier_orth hE6 hTE6 hLp hLm hCm hE0)

end CFSG.HardMathSupport.Meierfrankenfeld.Coordinator
