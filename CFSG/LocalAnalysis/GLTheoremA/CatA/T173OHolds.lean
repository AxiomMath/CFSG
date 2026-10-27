module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OTwMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OThreeHolds
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedShape
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelGen
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.SeitzReduction.TwistedE6Pilot

local notation "Γ₂" F => ModGL TwistTag.E6.tag F

theorem i173FactO_of_modelFactExcThree_of_famFive (hE8 : ModelFactExcThree .E8)
    (hFive : I173OOn famFive) : T173.I173FactO :=
  i173FactO_of_families i173OOn_famExcSplit i173OOn_famSpSplit
    (i173OOn_famThree_of_modelFactExcThree modelFactExcThree_F4 modelFactExcThree_E6
      modelFactExcThree_E7 hE8)
    i173OOn_famTwE6 hFive

theorem i173FactO_of_famFive (hFive : I173OOn famFive) : T173.I173FactO :=
  i173FactO_of_modelFactExcThree_of_famFive modelFactExcThree_E8 hFive

theorem i173FactO_holds : T173.I173FactO :=
  i173FactO_of_famFive i173OOn_famFive

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
