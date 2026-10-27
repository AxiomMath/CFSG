module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Facts3312
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3313LT
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3314B
public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierA

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace Frontier331

theorem stmt3_3_13LT_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) : Stmt3_3_13LT_F4 :=
  stmt3_3_13LT_of_F4 Vol2Native.a37ForSQTKCat_proved a38Cat (stmt3_3_10_of_frontier h311)
    prop134E9He_holds Vol2.Ch10.SecB.factL33M11 Vol2.Ch10.SecB.factL4L5 factAutL45Sylow_holds
    KGHe.factAutHeSylow_holds (Lem3313B.step3_3_13Bender_of Vol2Native.a37ForSQTKCat_proved a38Cat)
    hObl

theorem stmt3_3_14_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One)
    (hI14 : Insp3_3_14B) : Stmt3_3_14_F4 :=
  stmt3_3_14_of_b_F4 a38Cat Vol2Native.a39ForSQTKCat_proved (stmt3_3_10_of_frontier h311)
    (stmt3_3_13LT_of_frontier_F4 h311 hObl) h8one hI14

theorem step3_3_12R_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat) :
    Step3_3_12R_F4 :=
  step3_3_12R_of_inputs_F4 (stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14)
    (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved) (a38ForSQTK_of_cat a38Cat)
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) (a312 hList)
    Vol2Native.a36ForSQTKCat_proved NQCat.lemma128One_holds

theorem step3_3_12RB_of_frontier_F4
    (h311 : Theorem311Stmt) (hObl : Obl3_3_13LT_F4) (h8one : Stmt3_3_8One) (hI14 : Insp3_3_14B)
    (hList : Vol2Native.A312ListFactsCat) :
    Step3_3_12RB_F4 :=
  step3_3_12RB_of_inputs_F4 (stmt3_3_14_of_frontier_F4 h311 hObl h8one hI14)
    (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved) (a38ForSQTK_of_cat a38Cat)
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) (a312 hList)
    Vol2Native.a36ForSQTKCat_proved NQCat.lemma128One_holds

end Frontier331

end CFSG.Quasithin.H13
