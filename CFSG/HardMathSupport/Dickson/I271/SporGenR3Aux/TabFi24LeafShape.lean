module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeC
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeD
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeE
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Classes
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthGeneric
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Red
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.BorelTitsConstrained
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.RadicalQuot
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.RankThree.Native.ONSevenDefs
public import CFSG.RankThree.Native.ONSevenRestrict
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.Walter.Bender1970.S1
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.PSL2Facts
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2274
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8137
public import Certificates.Certificate8138
public import Certificates.Certificate8139
public import Certificates.Certificate8140
public import Certificates.Certificate8141
public import Certificates.Certificate8145
public import Certificates.Certificate8146
public import Certificates.Certificate9124

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

set_option linter.unusedSectionVars false


theorem shapeRkAt_fi24Rep3 (i : Fin 5) :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (fi24Rep3 i) := by
  fin_cases i
  · exact TabFi24.shapeRkAt_fi24Rep3_zero
  · exact TabFi24.shapeRkAt_fi24Rep3_one
  · exact TabFi24.shapeRkAt_fi24Rep3_two
  · exact TabFi24.shapeRkAt_fi24Rep3_three
  · exact TabFi24.shapeRkAt_fi24Rep3_four

theorem leafShape_Fi24_three : LeafShape .Fi24Prime 3 :=
  leafShape_Fi24_of_reps Fi24Sylow.fi24ThreeClasses_holds shapeRkAt_fi24Rep3

end CFSG.HardMathSupport.Dickson.I271
