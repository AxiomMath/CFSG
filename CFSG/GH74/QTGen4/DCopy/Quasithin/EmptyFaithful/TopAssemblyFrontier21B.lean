module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.Gap6Dec12Asm
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146zRShape
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146zXMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153QSL4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SzMSC12
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.TopAssemblyFrontier21A
public import CFSG.Quasithin.Background.FLcLnInv
public import CFSG.Quasithin.Background.FLcLnOver
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.Background.Harris.HoldsDimensionOnly
public import CFSG.Quasithin.Background.S1549EC
public import CFSG.Quasithin.EmptyFaithful.Der6CMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Cl4Fin
public import CFSG.Quasithin.EmptyFaithful.LRed2Eb
public import CFSG.Quasithin.EmptyFaithful.S143Top12
public import CFSG.Quasithin.EmptyFaithful.S146xNT
public import CFSG.Quasithin.EmptyFaithful.S146yA6Idx
public import CFSG.Quasithin.EmptyFaithful.S146zFGeom
public import CFSG.Quasithin.EmptyFaithful.S146zFourB
public import CFSG.Quasithin.EmptyFaithful.S146zGMain
public import CFSG.Quasithin.EmptyFaithful.S146zHA
public import CFSG.Quasithin.EmptyFaithful.S146zLFin
public import CFSG.Quasithin.EmptyFaithful.S146zMFin
public import CFSG.Quasithin.EmptyFaithful.S146zNTwoF
public import CFSG.Quasithin.EmptyFaithful.S146zQMain
public import CFSG.Quasithin.EmptyFaithful.S146zUZMain
public import CFSG.Quasithin.EmptyFaithful.S146zWL
public import CFSG.Quasithin.EmptyFaithful.S146zYHolds
public import CFSG.Quasithin.EmptyFaithful.S153LNdTop
public import CFSG.Quasithin.EmptyFaithful.S153LTop
public import CFSG.Quasithin.EmptyFaithful.SBc15Final
public import CFSG.Quasithin.EmptyFaithful.SzN25Top
public import CFSG.Quasithin.EmptyFaithful.SzN28X0Main
public import CFSG.Quasithin.EmptyFaithful.SzN29Chain
public import CFSG.Quasithin.EmptyFaithful.SzPS8FromG93
public import CFSG.Quasithin.EmptyFaithful.SzPS8Res

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.S143 CFSG.Quasithin.S152N
  CFSG.Quasithin.S152N2 CFSG.Quasithin.Gap6 CFSG.Quasithin.B69 CFSG.Quasithin.S153E
  CFSG.Quasithin.Insp7

structure QtfeFrontier21PartB_F4 : Prop where
  i49 : Stage15349Core
  h14316 : StageTheorem14316
  h146 : StageSection146_F4

theorem qtfe_frontier21_partB_F4
    (PA : QtfeFrontier21PartA_F4) : QtfeFrontier21PartB_F4 := by
  obtain ⟨-, -, -, -, hMS, -, hGoldP, -, hB42, -, hD37, hI5, -, -, -, -, -, -, hA3, hE22C, -,
      i10ListN, hB51, -, -, -, -, -, -, hC129, hC27, hF618, -, hG2c, h1413, -, -, hinsp, -, h11, -,
      -, h113, -, -, -, hI16, hA8, -, -, -, -, -, -, h56, -, -, -, hD391, -, -, hD36, -, -, hD321,
      hD310, hI4, h35, -, -, -, -, -, -, -, iF1432, -, h14620, -, h14622, h1461Six, h1463Four⟩ := PA

  have h12Big : NoE9Z4LargeBig_F4 :=
    noE9Z4LargeBig_proved_corr_F4 h35 hA3.1 hA3.2.1 hA3.2.2 hD36 hD37 hD321 hI5 hD310 hD391 hI4
      (goldschmidtCentralAbelianBound_of_charTwoLargePair hGoldP) hE22C.toNoN hF618 hC27 hMS
      (stage1463_two_of h1461Six) (stage1463_three_proof h1413) h1463Four

  have h134He : EmptyFaithfulMultiple.Prop134E9He := prop134E9He_holds

  have h12P : Stage14612PartP_F4 :=
    stage14612PartP_of_class_F4 (stage14612Class_of_lemma1435 h35)
      (noE9Z4_of_big_F4 h35 stage1461Five h12Big)

  obtain ⟨-, -, h14615, -, h14617⟩ :=
    stages14613_to_14617_of_SBc17K_cert_noUK_solDec_F4 hC27 stage1461Two stage1461Five
      (stage14612PartP_of_class_F4 (stage14612Class_of_lemma1435 h35)
      (noE9Z4_of_big_F4 h35 stage1461Five h12Big)) h1463Four H13.VolI.a36ForSQTK_holds hA3.2.1 input14613AP_proof (input14613B1P_of_actC input14613B1ActC_proved) input14613B2P_proved (input14614SolDec_proved H13.VolI.a36ForSQTK_holds hA3.1)
      (input14614Shape_proved_F4 h12P H13.VolI.a36ForSQTK_holds
        (S146zX.input14614Lists_of_prop134_F4 h12P hA3.1 hA3.2.1 hD36 hD37 hD321 hI5 hD310 hD391 hI4
          h134He S146zY.prop134Five_holds)
        S146zT.input14614NoSz_proved)
      (SBc16.input14615SetupFourP_of_R (S146zU.input14615SetupFourR_proved asA21SQTKSection h56 hA3.1 hA3.2.1 hD36 hD37 hD321 hI5 H13.VolI.a36ForSQTK_holds sqtkList3Dvd_proved S146zT.input14614NoSz_proved)) FixR.input14615FixR_proved (S146zW.input14615ContraOuterE_proved hC129 (fun G _ _ => a3Orbits_of_a37_a38 hA3.1 hA3.2.1) h56
        asA21SQTKSection) SBc15.input14616Weak_proved input14617FstarK_holds

  have h1469W : Stage1469W :=
    stage1469W_proved hA3.1 hA3.2.1 hA3.2.2 hE22C.toNoN (stage1463_two_of h1461Six)
      (stage1463_three_proof h1413) h1463Four

  have h1469 : Stage1469 := stage1469_of_W h1469W

  have h14610FiveW : Stage14610FiveW_F4 :=
    stage14610FiveW_of_narrow_inputs_H_corr_F4 h1469W hF618 hC27 hMS stage1463_one_proof
      (stage1463_two_of h1461Six) (stage1463_three_proof h1413) h1463Four i10ListN
      input14610PermFixedA6_holds input14610PermFixedA7_holds input14610PermA7Fixed_holds

  have h14610Five : Stage14610Five_F4 := stage14610Five_of_W_F4 h14610FiveW

  have h14624 : Stage14624 :=
    stage14624_of_fine_inputs_v2 stage1461Five (stage14621_of_a3 hA3.1 hA3.2.1 hA3.2.2) h14622 input14624U1_proof
      input14624U3_proof input14624KMoves_proof
      (input14624Geom_of (LRed5.noFaithfulFF_of_b56 h56 (stage14621_of_a3 hA3.1 hA3.2.1 hA3.2.2)) (stage14621_of_a3 hA3.1 hA3.2.1 hA3.2.2) h14622)
      input14624ThreeA_proof
      input14624ThreeB_proof (input14624ThreeC_of input14624NonFF_proof) (input14624ThreeD_of (input14624ThreeDAsym_of h1463Four stage1461Five input14624U1_proof input14624U3_proof input14624KMoves_proof input14624ThreeDAsymTwo_proof)) input14624Two_proved input14624NotTwoGroup_proof input14624FourRank_proof (input14624FourA_of h1463Four) (input14624FourB_of h1463Four)

  have i49 : Stage15349Core :=
    S1549E.stage15349Core_of_remaining_inputs h11 h113 hB51 hB42 (S153L.input49I_holds h113 h56) (SzN25.input49K_holds h113 h56 hG2c) (SzN19.input49L_holds h113 h56) S1549E.lnParabolicOvergroups_holds
      (S153L.lnSumNatDual_holds hB51 hI16 hA8) S1549E.lnInvariantParabolic_holds (SzN20.eRankOne_of_borel h113 h56 (SzN21.rankTwoBorel_holds hG2c))
      (l2OffenderNatural_of_b51 hB51 FFC.b58Inputs)

  have hg93 : G11.G93StmtDimensionOnly := CFSG.Quasithin.G11.Harris.g93StmtDimensionOnly_holds

  have hG112S : SzPS8.TheoremG112FixS := SzPS8.theoremG112FixS_of_g93 asA21SQTKSection h56 hg93

  have h14315 : S143.Lemma14315 := lemma_14_3_15_of_lemma1435_solv h11 h113 h35 (SzN28.lemma14315Solvable_of_hP h11 h113
      (SzPS8.lemma14315SolvableS8_of_g112S hG112S h11 h113 h35 H13.VolI.a36ForSQTK_holds hA3.1 hA3.2.2
        hE22C.toNoN iF1432)) (SzN31.g94StmtSolv_of_T SzN32.sylowGL6NoCover_proved)

  have hinspW2 : S143.Lemma14322InspectW2 :=
    S143.InspW2.lemma14322InspectW2_of_list lemma115_3_List_native

  have h14316 : StageTheorem14316 :=
    stageTheorem14316_of_inputs12
      ⟨h11, h113, h14315, hA3.1, hA3.2.2, lemma115_3_List_native, hinsp, hinspW2⟩

  have h146 : StageSection146_F4 :=
    stageSection146_of_inputs_thirteen_central_F4 hA3.1 hA3.2.1 hA3.2.2 h1413 h11 h113 (goldschmidtCentralAbelianBound_of_charTwoLargePair hGoldP) h14615
      h14617 h14620 h14622 (stage146D4A6_of asI231A6_holds) h14624 h1469 h14610Five h1463Four

  exact ⟨i49, h14316, h146⟩

end CFSG.Quasithin
