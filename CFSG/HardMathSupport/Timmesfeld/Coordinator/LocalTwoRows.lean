module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4Four
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6Four
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4ThreeSix
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6Three
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4Assembly
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4Six
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.E8Five
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Main
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicONSeven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenFinal
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.E8Phi5
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoRigid
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenEbarData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporSuz
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporTh
public import CFSG.Perm.ChainByOrder
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.KF4.B2Frame
public import CFSG.RankThree.PartOne.KF4.EvenDescent
public import CFSG.RankThree.PartOne.KLR.StarRad
public import CFSG.RankThree.PartOne.TCX.LayerEngineG

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census

set_option linter.unusedSectionVars false


theorem localTwoBalanceSporadicGtFive_of_open_rows
    (hFi7 : SporadicTwoPairHolds .Fi24Prime 7)
    (hB7 : OPrimeCoreLeTwoAt 7 (NativeSporadic.Carrier .B))
    (hM13 : SporadicTwoPairHolds .M 13) : LocalTwoBalanceSporadicGtFive := by
  have hB : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : SporadicOuterLeTwo := Proving.sporadicOuterLeTwo_holds
  have hBM : SporadicBMData := sporadicBMData_holds
  refine localTwoBalanceSporadicGtFive_of_rest hB hOut (sporadicTwoPair_of_sq_dvd hBM)
    { He_seven := sporadicTwoPairHolds_He_seven hB hOut
      ONan_seven := CFSG.HardMathSupport.Dickson.LocalTwoBalance.sporadicTwoPairHolds_ONan_seven
      Fi24Prime_seven := hFi7
      Co1_seven := sporadicTwoPairHolds_of_onePair hB hOut Nat.prime_seven (by norm_num)
        ⟨sporadicOPrimeHolds_Co1_seven, sporadicOuterHolds_Co1 7⟩
      Th_seven := sporadicTwoPairHolds_of_onePair hB hOut Nat.prime_seven (by norm_num)
        ⟨sporadicOPrimeHolds_Th_seven, sporadicOuterHolds_Th 7⟩
      B_seven := sporadicTwoPairHolds_B_seven_of_oPrime hB hBM hB7
      M_seven := sporadicTwoPairHolds_of_onePair hB hOut Nat.prime_seven (by norm_num)
        ⟨sporadicOPrimeHolds_M_of_gmat (oPrimeCoreTrivialAt_seven_Gmat_of_classes
          MonsterSevenCensus.monsterSevenClasses), sporadicOuterHolds_M 7⟩
      J4_eleven := sporadicTwoPairHolds_J4_eleven
      M_eleven := sporadicTwoPairHolds_of_onePair hB hOut (by norm_num) (by norm_num)
        ⟨sporadicOPrimeHolds_M_eleven, sporadicOuterHolds_M 11⟩
      M_thirteen := hM13 }

theorem localTwoBalanceSimpleGtFive_of_open_rows
    (hE6e6 : InnerPlaneBalanceAt .E6 6)
    (hE8e10 : InnerPlaneBalanceAt .E8 10) (hE8e12 : InnerPlaneBalanceAt .E8 12)
    (hFi7 : SporadicTwoPairHolds .Fi24Prime 7)
    (hB7 : OPrimeCoreLeTwoAt 7 (NativeSporadic.Carrier .B))
    (hM13 : SporadicTwoPairHolds .M 13) : LocalTwoBalanceSimpleGtFive :=
  localTwoBalanceSimpleGtFive_of_families (localTwoBalanceDefCharGtFive_of_dFourImage
      DFour.dFourPrimeCentralizerInImage_holds)
    (localTwoBalanceCrossCharGtFive_of_rows ReeF4Big.reeF4InnerPlaneBalance_holds
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.innerPlaneBalanceAt_trialityD4_three
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.innerPlaneBalanceAt_trialityD4_six
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.innerPlaneBalanceAt_F4_three
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.innerPlaneBalanceAt_F4_four
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.innerPlaneBalanceAt_F4_six
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.innerPlaneBalanceAt_E6_four hE6e6
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.innerPlaneBalanceAt_twistedE6_three
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.innerPlaneBalanceAt_twistedE6_four
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.innerPlaneBalanceAt_E8_five hE8e10 hE8e12)
    (localTwoBalanceSporadicGtFive_of_open_rows hFi7 hB7 hM13)

end CFSG.HardMathSupport.Timmesfeld.Coordinator
