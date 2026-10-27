module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJFinal
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ChevFrontier
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.FinalSmall
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.J3
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Final
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Model
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22Three
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi24Prime
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McL
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Suz
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ON
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HN
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Ly
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Th
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.B
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.M
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ

section Assembly

theorem kFactZJFactorization_holds : CFSG.LocalAnalysis.RankThreeTheoremC.KFactZJFactorization :=
  kFactZJFactorization_of_ffChev (HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffChevModuleTheorem_of
      (HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadic_of_each
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_J3
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Co1
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Co2
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Co3
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Fi22
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Fi23
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Fi24Prime
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_McL
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Suz
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_ONan
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_HN
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Ly
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Th
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_B
          HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_M)
      (HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOdd_of_nodes
          HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOddExceptional
          HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOddSmall))

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ
