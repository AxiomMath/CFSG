module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporHe
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporJ4
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporMcL
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporJ3
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporHN
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo2
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo3
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporFi22
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporSuz
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporLy
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporFi23
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporFi24
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo1
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporTh
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3He
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Top
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
public import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Pair
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvSound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24Tc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEHj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRep
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoONan
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzRowAtlas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartOne.Mult.Sec68
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestNative
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.OrderCheckF
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.Sporadic.Fi24
public import CFSG.Sporadic.Ly.ThreeBSpec
public import CFSG.Sporadic.Recognition.HNMultiplier
public import CFSG.Sporadic.Recognition.LyonsAS44Quat
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelYAut
public import CFSG.Sporadic.Recognition.LyonsFinalDist2
public import CFSG.Sporadic.Suz
public import Certificates.Certificate131101Base
public import Certificates.Certificate13620Base
public import Certificates.Certificate13622Base
public import Certificates.Certificate7233Base

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def restNames12 : Finset TauCeti.SporadicName :=
  {.Suz, .Co1, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime, .HN, .Ly, .Th, .B, .M}

theorem sporNoPumpup_of_rest12 (hR : ∀ name ∈ restNames12, SporNoPumpup name) :
    ∀ name ∈ restNames, SporNoPumpup name := by
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hSpM := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  intro name hname
  by_cases h12 : name ∈ restNames12
  · exact hR name h12
  · have : name = .He ∨ name = .J4 ∨ name = .McL ∨ name = .J3 := by
      revert hname h12
      cases name <;> decide
    rcases this with rfl | rfl | rfl | rfl
    · exact sporNoPumpup_He hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_J4 hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_McL hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_J3 hSpM inputONGroup_holds hOut hbr

theorem gapFinalPumpup_of_open12 (hR : ∀ name ∈ restNames12, SporNoPumpup name)
    (h1 : LieDownChev) (h2 : LieNoHatSix) : GapFinalPumpup :=
  gapFinalPumpup_of_open16 (sporNoPumpup_of_rest12 hR) lieOrderBridge_holds h1 h2

@[expose] def restNamesOpen : Finset TauCeti.SporadicName :=
  {.B, .M}

theorem sporNoPumpup_of_restOpen (hR : ∀ name ∈ restNamesOpen, SporNoPumpup name) :
    ∀ name ∈ restNames12, SporNoPumpup name := by
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hSpM := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  intro name hname
  by_cases h6 : name ∈ restNamesOpen
  · exact hR name h6
  · have : name = .HN ∨ name = .Co2 ∨ name = .Co3 ∨ name = .Fi22 ∨ name = .Suz ∨ name = .Ly ∨
        name = .Fi23 ∨ name = .Fi24Prime ∨ name = .Co1 ∨ name = .Th := by
      revert hname h6
      cases name <;> decide
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sporNoPumpup_HN hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_Co2 hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_Co3 hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_Fi22 hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_Suz hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_Ly hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_Fi23 hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_Fi24 hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_Co1 hSpM inputONGroup_holds hOut hbr
    · exact sporNoPumpup_Th hSpM inputONGroup_holds hOut hbr

theorem gapFinalPumpup_of_openSpor (hR : ∀ name ∈ restNamesOpen, SporNoPumpup name)
    (h1 : LieDownChev) (h2 : LieNoHatSix) : GapFinalPumpup :=
  gapFinalPumpup_of_open12 (sporNoPumpup_of_restOpen hR) h1 h2

end CFSG.HardMathSupport.Solomon.Coordinator
