module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.F112SMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtFlip4Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23E9Leaves
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23P4Wire
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtN204Wire
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.LRed9Quad
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Z6E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153QPE3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SzMSC3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SzMSC4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SzMSC5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515dF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.TopAssemblyFrontier21C
public import CFSG.Quasithin.Background.F918G4
public import CFSG.Quasithin.EmptyFaithful.FLc2MLCtx
public import CFSG.Quasithin.EmptyFaithful.FLc3Nat
public import CFSG.Quasithin.EmptyFaithful.FLc3SumCtx
public import CFSG.Quasithin.EmptyFaithful.FLc4MFrat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCert4193
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamTop
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9CompList
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Final
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Five2cMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQMain
public import CFSG.Quasithin.EmptyFaithful.S151S8BM11J
public import CFSG.Quasithin.EmptyFaithful.S151S8C2D
public import CFSG.Quasithin.EmptyFaithful.S151S9TFin
public import CFSG.Quasithin.EmptyFaithful.S151T4
public import CFSG.Quasithin.EmptyFaithful.S152He12J
public import CFSG.Quasithin.EmptyFaithful.S152He3Main
public import CFSG.Quasithin.EmptyFaithful.S152He4Main
public import CFSG.Quasithin.EmptyFaithful.S152He5Par
public import CFSG.Quasithin.EmptyFaithful.S152HeProp134
public import CFSG.Quasithin.EmptyFaithful.S152RCent3
public import CFSG.Quasithin.EmptyFaithful.S152TMain
public import CFSG.Quasithin.EmptyFaithful.S153ILemma122
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Final
public import CFSG.Quasithin.EmptyFaithful.SzF53DichAsm2
public import CFSG.Quasithin.EmptyFaithful.SzN2Main
public import CFSG.Quasithin.EmptyFaithful.T1515dD
public import CFSG.Quasithin.EmptyFaithful.T1521STop
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7Top

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.S143 CFSG.Quasithin.S152N
  CFSG.Quasithin.S152N2 CFSG.Quasithin.Gap6 CFSG.Quasithin.B69 CFSG.Quasithin.S153E
  CFSG.Quasithin.Insp7

structure QtfeFrontier21PartD_F4 : Prop where
  hR : StageRankNotTwo_F4

theorem qtfe_frontier21_partD_F4
    (PA : QtfeFrontier21PartA_F4) (PC : QtfeFrontier21PartC_F4) : QtfeFrontier21PartD_F4 := by
  obtain ⟨-, -, -, -, hMS, -, hGoldP, hHay, hB42, -, -, -, -, -, -, -, -, -, hA3, -, hcover, -,
      hB51, xzpInv, xautFixSimple, -, xcentMaxSimple, xmlDHardB, hB113, hC129, hC27, -, -, -, h1413,
      h1416, h1417, -, -, -, -, -, h113, -, -, -, hI16, hA8, -, -, -, hF318, hI25, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := PA

  have h134He : EmptyFaithfulMultiple.Prop134E9He := prop134E9He_holds

  have h126C := PC.h126C

  have h1414 := PC.h1414

  have h15111 := PC.h15111

  have h1511one := PC.h1511one

  have h1512four := PC.h1512four

  have h157 := PC.h157

  have h158 := PC.h158

  have h159 := PC.h159

  have h15CE := PC.h15CE

  have h319 := PC.h319

  have hD := PC.hD

  have hN := PC.hN

  have hStep := PC.hStep

  have hT316 := PC.hT316

  have hT317 := PC.hT317

  have xb42ListF := PC.xb42ListF

  have xcompList := PC.xcompList

  have xl2Block := PC.xl2Block

  have xlj := PC.xlj

  have xrankTwoExclF := PC.xrankTwoExclF

  obtain ⟨-, h1515, -, h1519, h15112, h15113, h15114⟩ :=
    LRed9.stage151_of_inputs_ce_FE hT316 hT317 h1413 h319 h1414 h1416 h1417 hD hN hStep h157 h158
      h1511one h1512four

  have hI20' : Lemma15120InputU_F4 := lemma15120InputU_of_named_inputs_F4 xlj
    (input15120_pair_of_faithful xb42ListF xrankTwoExclF).1 xl2Block
    (input15120_pair_of_faithful xb42ListF xrankTwoExclF).2 input15120L45_holds
    (S151TC.input15120TwoB_of_l3res_corr_F4 hA3.1 hA3.2.1 hC27 hC129 hMS S151TC.l3ResCorr_holds) xcompList
    (input15120MLA_holds hA3.1 hA3.2.1) (input15120MLB_holds hA3.2.1)
    (input15120MLC_of_simple xautFixSimple xcentMaxSimple)
    (input15120MLD_of_simple xautFixSimple xcentMaxSimple xmlDHardB) input15120MLE_holds

  have hI21' : Lemma15121InputU_F4 :=
    lemma15121InputU_of_F4 (struct15121_holds hA3.1 hA3.2.1) hI20' h1416 h15CE

  have h2c : Five2cTrivial :=
    H23P4.five2cTrivial_of (theoremC118_of_noOuter noOuterFact) h126C hA3.1 hA3.2.1

  have hNoE9 : SixFiveNoE9_F4 :=
    E9.sixFiveNoE9_of_leaves_F4 hA3.1 hA3.2.1 as116Statement h1416 h15CE h159 h15113 h15114 xlj
      (input15120_pair_of_faithful xb42ListF xrankTwoExclF).1 xl2Block
      (input15120_pair_of_faithful xb42ListF xrankTwoExclF).2 input15120L45_holds
      (S151TC.input15120TwoB_of_l3res_corr_F4 hA3.1 hA3.2.1 hC27 hC129 hMS S151TC.l3ResCorr_holds)
      (E9.input15120CompListCoarse_holds lemma115_3_List_native hA3.1 hA3.2.1 hB42 xlj
        (input15120_pair_of_faithful xb42ListF xrankTwoExclF).1
        (theoremC118_of_noOuter noOuterFact) h126C h1416 h15CE)
      (input15120MLA_holds hA3.1 hA3.2.1) (input15120MLB_holds hA3.2.1)
      typeCutBlock1521 typeCutComp1521 E9.typeCutCompAlt1521 (E9.famE9_of hA3.1 hA3.2.1)
      H23P4.p4Rows_of_certs (theoremC118_of_noOuter noOuterFact) h126C

  have hFive : Lemma15123FiveInputV := H23P4.lemma15123FiveInputV_of_certs h2c

  have h23 : Lemma15123Standalone_F4 :=
    lemma15123Standalone_of_fiveV_F4 hA3.1 hA3.2.1 hA3.2.2 hNoE9 h15CE h159 h15113 h15114 hI20' hI21'
      hFive

  have hX151 : Inputs151XR12Corr_F4 :=
    { lj := xlj,
      b42List := (input15120_pair_of_faithful xb42ListF xrankTwoExclF).1,
      l2Block := xl2Block,
      rankTwoExcl := (input15120_pair_of_faithful xb42ListF xrankTwoExclF).2,
      twoB := S151TC.input15120TwoB_of_l3res_corr_F4 hA3.1 hA3.2.1 hC27 hC129 hMS S151TC.l3ResCorr_holds,
      compList := xcompList,
      mlA := input15120MLA_holds hA3.1 hA3.2.1,
      mlB := input15120MLB_holds hA3.2.1,
      mlC := input15120MLC_of_simple xautFixSimple xcentMaxSimple,
      mlD := input15120MLD_of_simple xautFixSimple xcentMaxSimple xmlDHardB,
      dichotomy := input15122Dichotomy_holds,
      l3WreathStar := input15122L3WreathStar_holds (theoremC118_of_noOuter noOuterFact) h126C hA3.1 hA3.2.1,
      threeCLoc := input15122ThreeCLoc_of_residue input15122ThreeCLocB_holds xcentMaxSimple,
      threeCZL2 := input15122ThreeCZL2_of_loc hA3.1 hA3.2.1 rankTwoSimpleNotA38_holds (input15122ThreeCZL2Loc_of_simple xautFixSimple xzpInv),
      threeEFlip4 := input15122ThreeEFlip4_of_star_F4 (theoremC118_of_noOuter noOuterFact) h126C hA3.1 hA3.2.1 l45NotA38Type_holds
        (input15122ThreeEFlip4Star_holds_F4 h23 hA3.1 hA3.2.1 H13.VolI.a36ForSQTK_holds hF318 l45NotA38Type_holds
          knownFacts15122Types_final.l42),
      threeDHSRu := input15122ThreeDHSRu_of_local_corr_F4 hA3.1 hA3.2.1 hMS h1416 (input15122HSRuLocalCorr_of_combined input15122HSRuModels_holds),
      threeDM11 := input15122ThreeDM11_of_simple hA3.1 hA3.2.1 S151S8M11.input15122M11Normalizer_holds,
      threeDLoc := input15122ThreeDLoc_of_simple (input15122ThreeDLocS_proved S151S9T.threeDChecks_cert),
      threeDZL2 := input15122ThreeDZL2_of_loc hA3.1 hA3.2.1 sporadicSixNotA38_holds (input15122ThreeDZL2Loc_of_simple xautFixSimple xzpInv),
      sevenV2InQ := input15124SevenV2InQ_of knownFacts15122Types_final h15CE hA3.1 hA3.2.1,
      offenderTransfer := input15128OffenderTransfer_holds,
      ml28 := input15128ML_holds,
      natural := input15128Natural_holds,
      sumNatDual := input15128SumNatDual_holds,
      zDiagonal := input15129ZDiagonal_holds,
      zOrder := input15129ZOrder_holds,
      endNode := input15129EndNode_holds,
      msHyp := input15129MSHyp_holds,
      notC134 := input15129NotC134Corr_of_res input15129NotC134ResCorr_holds,
      mFrattini := input15129MFrattini_of h159 }

  obtain ⟨hI20, hI22, hI24, hI28, hI29⟩ := lemma151XR12_inputs_of_corr_F4 hX151 h159 h1416 h15CE hMS hC27
    (theoremC118_of_noOuter noOuterFact) h126C hA3.1 hA3.2.1 hF318 H13.VolI.a36ForSQTK_holds knownFacts15122Types_final

  have hI27 : Lemma15127InputU := lemma15127InputU_of hB51 hI16 hA8 h1416 h15CE

  have hI21 : Lemma15121InputU_F4 := lemma15121InputU_of_F4 (struct15121_holds hA3.1 hA3.2.1) hI20 h1416 h15CE

  have h15115 : StageTheorem1515_F4 :=
    LRed9.theorem1515_of_inputs_ce3_FE_F4 hA3.1 hA3.2.1 hA3.2.2 h23 hT316 hT317 h1413 h319 h1414 h1416
      h1417 hD hN hStep h157 h158 h1511one h1512four hI20 hI21 hI22 hI24 hI25 hI27 hI28 hI29

  have hOrb : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], A3Orbits G :=
    fun _ _ _ => a3Orbits_of_a37_a38 hA3.1 hA3.2.1

  have hOrb0 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G :=
    fun _ _ _ => a3Orbits_of_a37_a38 hA3.1 hA3.2.1

  have hDich2 : F53Dichotomy2 := F53.Stellmacher.f53Dichotomy2_holds

  have hF204 : He9.Input15204F112Untw := CFSG.Quasithin.Kleidman.F204.input15204F112Untw_holds

  have hR : StageRankNotTwo_F4 :=
    stageRankNotTwo_of_basic_inputs_ce28_F4 hB42 h113 h1416 h1515 h157 h158 h1519 h15111 h15112 h15113
      h15114 h15115 (He9.input15204F112_of_untw hF204)
      (He9.input15204Dichotomy_of_basic_F4 h113 h1515 h157 h1519 h15112 h15113 h15114 h15115 hA3.1 hA3.2.1 hA3.2.2
        (He9.input15204F112_of_untw hF204)) (He16.input15204BranchB_of_quasi_F4 H13.VolI.a36ForSQTK_holds (asc129StatementUsed_of_native hB113) (He17.input15204BranchBQuasi_proved_F4 hC27)) (asc129StatementUsed_of_native hB113) hA3.1 hA3.2.2 h134He hOrb lemma115_3_List_native insp15212_holds lemma122A_holds hC129 hC27 hcover hB51 hI16 hA8 input21Rank_of
      threeRankBlocks_holds input21ProperRank_of solvOvergroupsInBorel_holds (insp15224NoF2_proof hOrb0) hF318
      H13.VolI.a36ForSQTK_holds hA3.2.1 knownFacts15122Types_final cent3RankF2_holds (tail15215CoreW_of_certificates hOrb0) heNoSmallCommutatorModule_holds insp15227ParGood_holds (S152Z6.input15209Lift_proved_F4 (stageLemma15201_of_F4 h157 h15115) h1511one) hGoldP hHay F112S.titsRankCheck_cert (input15208F53Res_of_dichotomy2 hDich2)

  exact ⟨hR⟩

end CFSG.Quasithin
