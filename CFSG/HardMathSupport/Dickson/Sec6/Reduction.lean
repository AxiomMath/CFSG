module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3QuasiOpen
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2Full
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_5SFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.B3RedFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.L514BHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.I19Holds
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Fi
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2Reduce
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2A6
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2A7
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2M22
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2L2Main
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515CovHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.L514B1823Simple
public import CFSG.HardMathSupport.Solomon.Coordinator.L514CFix
public import CFSG.HardMathSupport.Solomon.Coordinator.L514VExp
public import CFSG.HardMathSupport.Solomon.Coordinator.L514VInn
public import CFSG.HardMathSupport.Solomon.Coordinator.L514Y0Model
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Holds
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
public import CFSG.HardMathSupport.Solomon.Coordinator.SignalizerFunctorInstance
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
public import CFSG.HardMathSupport.Solomon.Proving.LBLemma27
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL514VFix
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6OutFinal
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeFrontier
public import CFSG.Yardstones.M67c2c3e09a6b.Definitions
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Part3
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.AltMain

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns CFSG.Yardstones.M67c2c3e09a6b


theorem sec6Out_of_slots_and_residuals
    (h03 : LocalTwoBalanceThreeFive)
    (h04 : CFSG.HardMathSupport.Timmesfeld.LocalTwo.LocalTwoBalanceSimpleGtFive)
    (h05 : SporadicBpResiduals) (h09 : I271OpenFamilies)
    (hF254 : GenL3.Input25_4FactsNarrow)
    (h92 : Input9_2_3 innAutDerivedVocab) (h1431 : Input14_31_4 innAutDerivedVocab) :
    Sec6Out := by
  have h02 : LocalThreeBalanceSimpleFamilies :=
    ⟨CFSG.HardMathSupport.Timmesfeld.Coordinator.localThreeBalanceCrossChar_holds,
      CFSG.HardMathSupport.Timmesfeld.Coordinator.localThreeBalanceSporadic_holds⟩
  have h06 : LieCentralizerResiduals :=
    ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent,
      CFSG.HardMathSupport.Dickson.DefCharOuter.lieDefCharOuter⟩
  have hT112 : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112 :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
  have hTL2 : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableL2 :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
  have h2 : LocalTwoBalanceGtFive :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.localTwoBalanceGtFive_of_parts h04
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.localTwoBalanceAltGtFive_proved
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.localTwoBalanceLpEpsGtFive_proved
  have h3 : LocalThreeBalance :=
    localThreeBalance_of_simple_alt
      (localThreeBalanceSimple_of_families
        (CFSG.HardMathSupport.Timmesfeld.DefChar.localThreeBalanceDefChar_of_dFour
          (CFSG.HardMathSupport.Timmesfeld.DefChar.defCharInnerCoreFreeFamDFour_of_image
            CFSG.HardMathSupport.Timmesfeld.DFour.dFourPrimeCentralizerInImage_holds))
        h02.crossChar h02.sporadic)
      CFSG.HardMathSupport.Timmesfeld.Balance.Alt.localThreeBalanceAlt_proved
  have h21 : Prop21 :=
    prop21_of_localBalance CFSG.HardMathSupport.Timmesfeld.Balance.deltaOfLocalBalance_proved h3 h2
  have i1910 : Input19_10 :=
    input19_10_of_open h3 h2 h03.crossCharThree h03.sporadicThree h03.crossCharFive h03.sporadicFive
      u3EightTwoBalanceThree_holds weakLThreeEpsThree_holds fi22CoverFive_holds
      weakFi22Five_holds weakLFiveEpsFive_holds lFiveEpsFiveTwo_holds
  have h24 : Lemma24 :=
    lemma24_of_inputs lemma23_proved i1910 input19_3_1_holds
      (input11_2Full_of_tables hT112 hTL2 tables112Types_holds) (input19_5_2_of_simple
          isLocallyBalancedAbs_L2OddPow isLocallyBalancedAbs_A6 isLocallyBalancedAbs_A7
          isLocallyBalancedAbs_M22)
  have i271 : Input27_1K :=
    input27_1K_of_familiesRest hT112 hTL2 tables112Types_holds
      ⟨h09.nnHatSixRank, i271AutBalanceAltSix_holds, h09.nnOther, h09.altDiv, h09.altNdiv,
        h09.chevPBal, h09.chevPExc, h09.sporGen, h09.autBalanceON, h09.onLow, h09.chevQL34,
        h09.chevQ⟩
  have h31 : Lemma31 := lemma31_of_input27_1K i271
  have h515 : Lemma515 := lemma515_of_inputs gap515CentreK_holds
  have hI145 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_5 :=
    CFSG.HardMathSupport.Solomon.Proving.lemma27_input14_5_of_second
      (input14_5Second_of_lemma27
          (b3Cent_of_quasisimple
              (b3Quasi_of_open
                  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.bThreeRc_holds
                  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.bThreeRd_holds
                  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.bFiveNonCentral_holds
                  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.twoAPureKlein_three_Gmat
                  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.twoATwoCommuting_five_Gmat
                  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus.monsterSevenClasses
                  h05.j4Three h05.restPairs h06.semisimpleCent h06.defCharOuter))
          lemma514Cover_input18_1_holds)
  have hInputs : Inputs innAutDerivedVocab :=
    ⟨lemma514Cover_input18_1_holds, lemma514Cover_input18_2_holds,
      l514b_input18_3_23_simple CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds hI145,
      lemma514Cover_input18_3_4G_holds, input2_5_proved, h92, h1431, inputL3T_holds,
      inputL3fix_l514V, inputL3inn_holds, inputL3y0_holds, inputL3out_holds, inputL3fld_holds,
      lemma514Cover_inputL3rk_holds, inputL3iso_holds, lemma514Cover_inputL3size_holds,
      lemma514Cover_inputL3L2_holds, inputL2fld_holds, inputL2exp_holds,
      lemma514Cover_inputFixComp_holds, gap515CentreK_holds⟩
  have h514 : Lemma514 := lemma514_of_inputs innAutDerivedVocab hInputs
  exact sec6Out_final signalizerFunctorTheoremK_holds h21 h24 h31 h514 h515 hT112 hTL2 hF254

end CFSG.HardMathSupport.Dickson.Sec6
