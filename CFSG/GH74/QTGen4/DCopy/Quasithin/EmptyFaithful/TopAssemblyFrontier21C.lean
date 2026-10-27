module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.TopAssemblyFrontier21A
public import CFSG.Quasithin.Background.Harris.KFact2d.Holds
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtB42ListFMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockNarrow
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtLJMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2SwapMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111CMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Main
public import CFSG.Quasithin.EmptyFaithful.LRed10KerN
public import CFSG.Quasithin.EmptyFaithful.List115Native
public import CFSG.Quasithin.EmptyFaithful.S151CLTop
public import CFSG.Quasithin.EmptyFaithful.S151cFinal
public import CFSG.Quasithin.EmptyFaithful.SzOneNo3b
public import CFSG.Quasithin.Vol2.Ch3g316
public import CFSG.Quasithin.Vol2.Ch3xStep1414
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WHolds

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.S143 CFSG.Quasithin.S152N
  CFSG.Quasithin.S152N2 CFSG.Quasithin.Gap6 CFSG.Quasithin.B69 CFSG.Quasithin.S153E
  CFSG.Quasithin.Insp7

structure QtfeFrontier21PartC_F4 : Prop where
  h126C : TheoremC126
  h1414 : StageLemma1414
  hT316 : Theorem316StatementPerf
  hT317 : Theorem317StatementFE
  h319 : LRed9.Lemma319StatementCE
  hD : Description1512CE
  hN : Nilpotency1512CE
  h157 : StageLemma1517
  h158 : StageLemma1518
  h15CE : StageLemma1515CE
  h159 : StageLemma1519
  h1511one : StageLemma15111One
  hStep : Step1514Gen
  h1512four : StageLemma15112Four
  h15111 : StageLemma15111
  xlj : Input15120LJ
  xb42ListF : Input15120B42ListF
  xl2Block : Input15120L2Block
  xrankTwoExclF : Input15120RankTwoExclF
  xcompList : Input15120CompList

theorem qtfe_frontier21_partC_F4
    (PA : QtfeFrontier21PartA_F4) : QtfeFrontier21PartC_F4 := by
  obtain ⟨-, -, -, -, -, -, hGoldP, -, hB42, -, -, -, -, -, hE217N, hE213NS, hE215NS, -, hA3, hE22C,
      hcover, -, -, -, -, -, -, -, -, -, -, -, -, hG2c, h1413, h1416, h1417, -, hC, -, -, -, -,
      hB15P4, -, hComp69, -, -, -, -, -, -, -, -, h56, h116L2, -, -, -, -, -, -, -, -, -, -, -, -,
      -, hS311, hC58, -, -, -, -, -, -, -, -, -, -, -⟩ := PA

  have hB69 : B69One := B69.b69One_of_Sp4NoN hB42 hB15P4 asA21SQTKSection hE22C.toNoN B69.noStrongSp4

  have hE23NS : E2.E23Nonsolvable := GE23.e23Nonsolvable_of_inputs hB15P4 hComp69 hB69 hE22C.toNoN

  have hGen316 : Gen316 := Ch3g316.gen316_proved hB69 hE23NS

  have hAS316NS : AS316SylowNonsolvable := as316SylowNonsolvable_of_inputs hGen316

  have hE23S : E2.E23Statement := E2.e23Statement_of_nonsolvable hE23NS

  have hRF126 : C126.RadFreeStmt := C126.radFreeStmt_of_e22 hE22C.toNoN mult2Fact

  have h126C : TheoremC126 :=
    theoremC126_of_cases hE23S (fun _ _ _ _ _ => C126.Nat.natStmt_of_e23 hE23S hRF126)
      (fun _ _ _ _ _ => C126.a5Stmt_of_radFree hRF126)

  have hAS317NS : AS317SylowNonsolvable := LRed10.as317SylowNonsolvable_of_e23_noN hE23NS hE22C.toNoN

  have hD125 : D125NonsolvableSQTK := d125NonsolvableSQTK_of_b69One hB69

  have hShape319 : Lemma319Shape :=
    E23J.lemma319Shape_of_inputs (B69.b69Struct_main hB15P4 hComp69 (B69.asB69GenByMin_of hB15P4 hComp69)) hB69 hC58 hAS317NS hD125

  have hD15 : D15AsPrintedSQTK := d15AsPrintedSQTK_of_nonsolvable hD125

  have hE213 : E213Three := e213Three_of_nonsolvable hE213NS

  have hE215 : E215 := e215_of_nonsolvable hE215NS

  have h1414 : StageLemma1414 := S1414.lemma_1414_core h1413 hS311

  have hT316 : Theorem316StatementPerf :=
    theorem316StatementPerf_of_core_inputs hC58 hD15 hE213 hE215 hAS316NS

  have hT317 : Theorem317StatementFE := theorem317StatementFE_of_solvable hS311

  have h319 : LRed9.Lemma319StatementCE :=
    LRed9.lemma319StatementCE_of_inputs hC58 hD15 hAS316NS hD125 hShape319

  have h1511 : StageLemma1511 := stageLemma1511_of_theorem316Perf hT316 h1416

  have hD : Description1512CE := description1512CE_of h1511 h1414 h1416 h1417 hC

  have hN : Nilpotency1512CE := nilpotency1512CE_of h1511 h1414 h1416 h1417 hC

  have h157 : StageLemma1517 := stageLemma1517_of h1511 h1414 h1416 h1417 hC

  have h158 : StageLemma1518 := stageLemma1518_of h1511 h1414 h1416 h1417 hC

  have h15CE : StageLemma1515CE := stageLemma1515CE_of_description hD

  have h16CE : StageLemma1516CE := stageLemma1516CE_of hN

  have h159 : StageLemma1519 := stageLemma1519_of_ce_FE h1414 h1417 hT317 h1413 h15CE h16CE

  have hY15111 : He13.Input15111YRigid := Y15111.input15111YRigid_of_coreFree h15CE h158 h159 hE215 h1416
    (Y15111.input15111YCoreFree_of_list
      (F6.goldschmidtS3ListCat_of_charTwoLarge (F6.goldschmidtCharTwoLarge_of_pair hGoldP))
      F6.g22AmalgamShapeFact_holds F6.m12AmalgamShapeFact_holds F6.autM12AmalgamShapeFact_holds)

  have h1511one : StageLemma15111One := E217Wire.stageLemma15111One_of_rigid_narrow h15CE h158 h159 hE215 hE217N hY15111

  have hK2d : Gap6R2.KFact2dAtoms := CFSG.Quasithin.Background.Harris.KFact2d.kfact2dAtoms_holds

  have hOne : Gap6R2.NonBorelOutcomeOneW :=
    Gap6R2.nonBorelOutcomeOneW_of_v2d Res2.e215MemberW_holds (stageLemma15110_of_ce h1416 h15CE) h1511one
      hE22C.toNoN (fun _ _ _ => a3Orbits_of_a37_a38 hA3.1 hA3.2.1)
      (Gap6R2.nonBorelV2d_of_kfact2d hK2d (stageLemma15111_of_one h158 h159 h1511one))

  have hRes2 : Step1514GenResidual2 :=
    Gap6R2.step1514GenResidual2_of_outcomeOneW hOne hC58
      (B69.b69Struct_main hB15P4 hComp69 (B69.asB69GenByMin_of hB15P4 hComp69)) hB69 hD125 hD15
      h1413 h15CE h157 h158 (notDualFF1512_of_ce h1416 h15CE h158 h159)

  have hStep : Step1514Gen := step1514Gen_of_residual2 h159 hRes2

  have h1512four : StageLemma15112Four :=
    LRed9.stageLemma15112Four_of_gen h319 h1416 h15CE h158 h159 h16CE h1511one

  obtain ⟨-, h1515, -, h1519, h15112, h15113, h15114⟩ :=
    LRed9.stage151_of_inputs_ce_FE hT316 hT317 h1413 h319 h1414 h1416 h1417 hD hN hStep h157 h158
      h1511one h1512four

  have h15111 : StageLemma15111 := stageLemma15111_of_one h158 h1519 h1511one

  have xlj : Input15120LJ := input15120LJ_holds hA3.1 hA3.2.1 h1416 h15CE

  have xb42ListF : Input15120B42ListF := input15120B42ListF_holds hA3.1 hA3.2.1 xlj h56 hcover hG2c

  have xl2Block : Input15120L2Block := input15120L2BlockN_of_res_l2 (theoremC118_of_noOuter noOuterFact) h126C
    h116L2 xlj h1416 h15CE input15120WreathChar_holds (input15120L2BlockResC_holds hA3.1 hA3.2.1 hB42 xlj)

  have xrankTwoExclF : Input15120RankTwoExclF := Rk2.input15120RankTwoExclF_of' hA3.1 hA3.2.1 xl2Block
    (theoremC118_of_noOuter noOuterFact) h126C h1416 h15CE

  have xcompList : Input15120CompList := input15120CompList_holds lemma115_3_List_native hA3.1 hA3.2.1 hB42 xlj
    (input15120_pair_of_faithful xb42ListF xrankTwoExclF).1 (theoremC118_of_noOuter noOuterFact) h126C h1416 h15CE

  exact ⟨h126C, h1414, hT316, hT317, h319, hD, hN, h157, h158, h15CE, h159, h1511one, hStep, h1512four, h15111, xlj, xb42ListF, xl2Block, xrankTwoExclF, xcompList⟩

end CFSG.Quasithin
