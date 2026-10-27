module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3FrontierA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3316S
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3317
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3319G
public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierB

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace Frontier331

theorem step3_3_15R_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat) :
    Step3_3_15R_F4 :=
  step3_3_15R_of_F4 stmt3_3_6_of_frontier (stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14)
    (step3_3_12R_of_frontier_F4 h311 hObl h8one hI14 hList)

theorem stmt3_3_16_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat)
    (hC32 : ASInputs.AS_C_1_32_F4) : Stmt3_3_16_F4 :=
  L3316.stmt3_3_16_of_inputs_F4 stmt3_3_6_of_frontier
    (stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14) hC32 a38Cat
    Vol2Native.a39ForSQTKCat_proved B5.asB51_holds (stmt3_3_10_of_frontier h311)
    (step3_3_12RB_of_frontier_F4 h311 hObl h8one hI14 hList)
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

theorem stmt3_3_17_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat)
    : Stmt3_3_17_F4 :=
  stmt3_3_17_of_F4 stmt3_3_6_of_frontier (stmt3_3_8_of_frontier h8one)
    (stmt3_3_10_of_frontier h311) (step3_3_12R_of_frontier_F4 h311 hObl h8one hI14 hList)
    (stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14)

theorem stmt3_3_18_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat)
    (hC34 : C134L32Corr_F4) (h20 : Stmt3_3_20) : Stmt3_3_18_F4 :=
  L3318.stmt3_3_18_of_F4 (stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14)
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement a38Cat
    Vol2Native.a39ForSQTKCat_proved (step3_3_12R_of_frontier_F4 h311 hObl h8one hI14 hList)
    (step3_3_15R_of_frontier_F4 h311 hObl h8one hI14 hList) hC34 h20

theorem stmt3_3_19_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat)
    (hC34 : C134L32Corr_F4) (h20 : Stmt3_3_20) : Stmt3_3_19_F4 :=
  L3319.stmt3_3_19_of_F4 (stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14)
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement a38Cat
    Vol2Native.a39ForSQTKCat_proved (step3_3_12R_of_frontier_F4 h311 hObl h8one hI14 hList)
    (step3_3_15R_of_frontier_F4 h311 hObl h8one hI14 hList) hC34 h20 B5.asB51_holds
    VolI.asI16Cover_holds

end Frontier331

end CFSG.Quasithin.H13
