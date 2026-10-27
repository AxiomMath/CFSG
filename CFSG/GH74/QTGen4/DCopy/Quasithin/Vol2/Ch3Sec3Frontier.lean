module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Close
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3FrontierC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3G2Step28
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3313Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3324B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3325
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3327
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3330H
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3331E4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3332
public import CFSG.Quasithin.Vol2.Ch3Sec3Frontier

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace Frontier331

theorem stmt3_3_1A_of_frontier_F4
    (hD12 : Obl3_3_13D12_F4) (hC32 : ASInputs.AS_C_1_32_F4) (hC34 : C134L32Corr_F4)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) (hF : F6.TheoremF618Cat) :
    Stmt3_3_1A_F4 := by
  have hObl : Obl3_3_13LT_F4 :=
    Lem3313Q.obl3_3_13LT_of_D12_F4 Vol2Native.a37ForSQTKCat_proved a38Cat hD12
  have hI14 : Insp3_3_14B := Ins314.insp3_3_14B_of Vol2Native.a37ForSQTKCat_proved a38Cat
  have h8one : Stmt3_3_8One := stmt3_3_8One_of_b56 a38Cat Vol2Native.a39ForSQTKCat_proved
    asB56_holds VolI.a38TypesSLThree_holds
  have h38 : A38ForSQTKCat := a38Cat
  have h39 : A39ForSQTKCat := Vol2Native.a39ForSQTKCat_proved
  have h14 := stmt3_3_14_of_frontier_F4 theorem311 hObl h8one hI14
  have h20 := stmt3_3_20_of_frontier theorem311 hF a312List
  have hO24 := obs3_3_24_of_frontier_F4 theorem311 hObl h8one hI14 a312List hC32 hC34 hC27
    hF
  have hE := HatE.hatA6Embed_holds
  have hN := HatN.hatA6Normalizer_holds
  have hXS3 := HatX.fact3_3_25XS3Hat_of h38 h39 hE hN
  have hHat := HatB.insp3_3_25Hat_of h38 h39 (HatQ.insp3_3_25HatRest_of h38 h39 hE hN)
  have hS23 := step3_3_23_of_F4 h38 h39 h14 hC34
    (C4Fix3323.notCase4Corr3323_holds_F4 h38 h39 h14 h20 hC34)
  have hS24 := step3_3_24_of_F4 h38 h39 h14 hC34 h20
  have h23 := stmt3_3_23_of_F4 h38 h39 h20 hS23
  have h24 := stmt3_3_24_of_F4 h23 hO24 hS24
  have hF318 : A318Facts := a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds
  have hθ := fact3_3_25Theta_of hF318 VolI.a36ForSQTK_holds (a38ForSQTK_of_cat h38)
  have hX := CZA6.fact3_3_25XS3_of h38 h39 (CZA6.fact3_3_25XS3Rest_of h38 h39 B5.asB51_holds hXS3)
  have hT := ThreeL32.insp3_3_25Three_of h38 h39
    (ThreeL32.insp3_3_25ThreeRest_holds h38 h39 B5.asB51_holds)
  have hI := CZA6.insp3_3_27_of h38 h39 (CZA6.insp3_3_27Rest_holds h38 h39 B5.asB51_holds)
  have h25 := stmt3_3_25_of_F4 h38 h39 h14 h24 hθ hX hHat hT
  have h27 := stmt3_3_27_of_F4 h38 h39 h14 h25 factL32CentralInv_holds hI
  have hS28 := G2Step28.step3_3_28G2_of_F4 h38 h39 B5.asB51_holds h25 h27
  have h26 := stmt3_3_26_of_F4 h38 h39 h14 h25
  have h28L := stmt3_3_28L32_of_F4 h38 h39 h14 h23 h25 h26 h27
  have h29 := stmt3_3_29_of_F4 h38 h39 h14 h23 h25 h28L
  have h28TC := stmt3_3_28G2TC_of_F4 h38 h39 h14 h25 h26 h29 hS28
  have h28G := stmt3_3_28G2_of_F4 h25 h28TC
  have h30 := stmt3_3_30_of_h_F4 h38 h39 h14 h25 h28G h29
    (Lem3330H.insp3_3_30H_of h38 h39 B5.asB51_holds)
  have h31 := stmt3_3_31_of_F4 h38 h39 h14 h26 h27 h30 (Lem3331S.step3_3_31S_of_F4 h38 h39 h25 h27)
    (Lem3331E4.step3_3_31E4_of_F4 h38 h39 h25 h27)
  have h32 := stmt3_3_32_of_F4 h38 h39 h14 h20 h30 h31 (insp3_3_32Mod_holds h38 h39)
    (insp3_3_32Par_holds h38 h39)
  exact stmt3_3_1A_of_inputs_F4 h38 h39 h14 h30 h31 h32 (inspClose_holds h38 h39)

theorem stmt3_3_1_of_frontier_F4
    (hD12 : Obl3_3_13D12_F4) (hC32 : ASInputs.AS_C_1_32_F4) (hC34 : C134L32Corr_F4)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) (hF : F6.TheoremF618Cat) :
    Stmt3_3_1_F4 :=
  stmt3_3_1_of_F4 Vol2Native.a37ForSQTKCat_proved a38Cat Vol2Native.a39ForSQTKCat_proved
    (stmt3_3_1A_of_frontier_F4 hD12 hC32 hC34 hC27 hF)
    Cor332.stmt3_3_2MTwo_holds

end Frontier331

end CFSG.Quasithin.H13
