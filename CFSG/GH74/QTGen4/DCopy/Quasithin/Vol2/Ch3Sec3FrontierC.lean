module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3FrontierB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321QD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3322
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Obs3324
public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierC

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace Frontier331

theorem stmt3_3_21_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat) (hC34 : C134L32Corr_F4)
    (hF : F6.TheoremF618Cat) :
    Stmt3_3_21_F4 := by
  have h5 := stmt3_3_5_of a38Cat Vol2Native.a39ForSQTKCat_proved
  have h7 := stmt3_3_7_of a38Cat Vol2Native.a39ForSQTKCat_proved
  have h14 := stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hfQ : Step3_3_21fQ_F4 := L3321.step3_3_21fQ_of_F4 h7 h14 hGA
    (L3321.step3_3_21e_of_F4 h5 h14 hGA (L3321.step3_3_21d_of_F4 h5 h7 stmt3_3_9_of h14))
  exact stmt3_3_21_of_F4 h5 h7 stmt3_3_9_of (stmt3_3_13LT_of_frontier_F4 h311 hObl) h14
    (stmt3_3_18_of_frontier_F4 h311 hObl h8one hI14 hList hC34 (stmt3_3_20_of_frontier h311 hF hList))
    (stmt3_3_20_of_frontier h311 hF hList) B5.asB51_holds VolI.asI16Cover_holds a38Cat
    Vol2Native.a39ForSQTKCat_proved hGA (step3_3_15R_of_frontier_F4 h311 hObl h8one hI14 hList)
    hC34 (step3_3_12R_of_frontier_F4 h311 hObl h8one hI14 hList) hfQ

theorem stmt3_3_22_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) :
    Stmt3_3_22_F4 :=
  stmt3_3_22_of_F4 (stmt3_3_5_of a38Cat Vol2Native.a39ForSQTKCat_proved)
    (stmt3_3_7_of a38Cat Vol2Native.a39ForSQTKCat_proved) (stmt3_3_8_of_frontier h8one)
    (stmt3_3_10_of_frontier h311) (stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14)
    (stmt3_3_17_of_frontier_F4 h311 hObl h8one hI14 hList) a38Cat
    Vol2Native.a39ForSQTKCat_proved (a38ForSQTK_of_cat a38Cat)
    (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds) hC27

theorem obs3_3_24_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat)
    (hC32 : ASInputs.AS_C_1_32_F4) (hC34 : C134L32Corr_F4)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) (hF : F6.TheoremF618Cat) :
    Obs3_3_24_F4 :=
  obs3_3_24_of_F4 a38Cat Vol2Native.a39ForSQTKCat_proved B5.asB51_holds
    (stmt3_3_10_of_frontier h311) (stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14)
    (stmt3_3_16_of_frontier_F4 h311 hObl h8one hI14 hList hC32)
    (stmt3_3_19_of_frontier_F4 h311 hObl h8one hI14 hList hC34 (stmt3_3_20_of_frontier h311 hF hList))
    (stmt3_3_21_of_frontier_F4 h311 hObl h8one hI14 hList hC34 hF)
    (stmt3_3_22_of_frontier_F4 h311 hObl h8one hI14 hList hC27) hC32

end Frontier331

end CFSG.Quasithin.H13
