module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Set14
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtC137Stmt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Prod
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS1312R
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14Wire
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135W
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3X10Five
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.H13.GoldschmidtC137SQFinal
public import CFSG.Quasithin.Vol2.Ch3Sec3Frontier
public import CFSG.Quasithin.Vol2.GoldschmidtTD317
public import CFSG.Quasithin.Vol2.GoldschmidtTD32

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem U3.stmt13_3_14_of_open_F4
    (h_Stmt3_3_1 : CFSG.Quasithin.H13.Stmt3_3_1_F4)
    (h_Stmt12_2_2 : CFSG.Quasithin.H13.Stmt12_2_2_F4)
    (h_Stmt12_2_13 : CFSG.Quasithin.H13.Stmt12_2_13_F4)
    (h_Stmt13_3_2 : CFSG.Quasithin.H13.Stmt13_3_2_F4)
    (h_C137StatementFiveSQTK : CFSG.Quasithin.H13.U3.GC137.C137StatementFiveSQTK_F4)
    (h_Stmt5_2_3 : CFSG.Quasithin.H13.Stmt5_2_3_F4)
    (h_Res1328a : CFSG.Quasithin.H13.A5.Res1328a_F4)
    (h_Rest1327 : CFSG.Quasithin.H13.A5.Rest1327_F4)
    (h_U3LineComponentExclusion : CFSG.Quasithin.H13.U3.U3LineComponentExclusion_F4) :
    A6.Stmt13_3_14_F4 := by
  have h_E22StatementNoN := CFSG.Quasithin.e22StatementNoN_proved
  have h_Stmt13_2_7 := CFSG.Quasithin.H13.A5.stmt13_2_7_ofNoN_F4 (h331 := h_Stmt3_3_1)
      (h523 := h_Stmt5_2_3) (h1222 := h_Stmt12_2_2) (hE22 := h_E22StatementNoN) (hRes := h_Res1328a)
      (hrest := h_Rest1327)
  have h_Stmt13_3_6 := CFSG.Quasithin.H13.U3.stmt13_3_6_of_1332_F4 (h1332 := h_Stmt13_3_2)
      (h1222 := h_Stmt12_2_2) (h12213 := h_Stmt12_2_13) (h331 := h_Stmt3_3_1)
      (h1327 := h_Stmt13_2_7)
  have h_TheoremC58 := CFSG.Quasithin.theoremC58_proved
  have h_AS317Sylow := CFSG.Quasithin.as317Sylow_proved
  have h_AsB56 := CFSG.Quasithin.asB56_holds
  have h_QSporOutTwo := CFSG.Quasithin.qSporOutTwo_holds
  have h_QLiePRank := CFSG.Quasithin.R3c18.qLiePRank_holds
  have h_A318Facts := CFSG.Quasithin.a318Facts_of_two (qs := h_QSporOutTwo) (ql := h_QLiePRank)
  have h_Stmt13_3_4 := CFSG.Quasithin.H13.U3.stmt13_3_4_of_F4 (h1332 := h_Stmt13_3_2)
  have h_C137SQTKSupply := CFSG.Quasithin.H13.U3.GC137.c137SQTKSupply_holds
  have h_C137StatementFive := CFSG.Quasithin.H13.U3.GC137.c137StatementFive_of_sqtk_F4
      (h := h_C137StatementFiveSQTK) (hs := h_C137SQTKSupply)
  have h_Stmt13_3_10 := CFSG.Quasithin.H13.U3.stmt13_3_10_of_five_F4 (h1332 := h_Stmt13_3_2)
      (h1222 := h_Stmt12_2_2) (h1334 := h_Stmt13_3_4) (hC137 := h_C137StatementFive)
  have h_Stmt13_3_14d := CFSG.Quasithin.H13.U3.stmt13_3_14d_holds_F4 (h1332 := h_Stmt13_3_2)
      (h1336 := h_Stmt13_3_6)
  have h_Stmt3_2_3 := CFSG.Quasithin.H13.stmt3_2_3_proved
  have h_Set14ProducerA6 := CFSG.Quasithin.H13.A6.set14ProducerA6_of_F4 (h1332 := h_Stmt13_3_2)
      (h1222 := h_Stmt12_2_2) (h323 := h_Stmt3_2_3)
  have h_Set14ProducerL32 := CFSG.Quasithin.H13.L32NSet14.set14ProducerL32_of_inputs_F4
      (h1332 := h_Stmt13_3_2) (h1222 := h_Stmt12_2_2) (h323 := h_Stmt3_2_3) (h1334 := h_Stmt13_3_4)
  have h_Theorem311Stmt := CFSG.Quasithin.H13.Frontier331.theorem311
  have h_U3NondegLineCentralizer := CFSG.Quasithin.H13.U3.u3NondegLineCentralizer_of_comp_F4
      (h1332 := h_Stmt13_3_2) (h311 := h_Theorem311Stmt) (hK := h_U3LineComponentExclusion)
  have h_Set14ProducerU33 := CFSG.Quasithin.H13.U3.set14ProducerU33_of_F4 (h1332 := h_Stmt13_3_2)
      (hNL := h_U3NondegLineCentralizer)
  have h_Stmt13_3_14 := CFSG.Quasithin.H13.U3.stmt13_3_14_holds_F4 (h1332 := h_Stmt13_3_2)
      (h1336 := h_Stmt13_3_6) (hC58 := h_TheoremC58) (h317 := h_AS317Sylow) (h56 := h_AsB56)
      (hF := h_A318Facts) (h1310 := h_Stmt13_3_10) (hd := h_Stmt13_3_14d) (hA6 := h_Set14ProducerA6)
      (hL32 := h_Set14ProducerL32) (hU33 := h_Set14ProducerU33)
  exact h_Stmt13_3_14

end CFSG.Quasithin.H13
