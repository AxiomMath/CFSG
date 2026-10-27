module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528EKGHolds
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem528EMain

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.SL3Small Matrix
open scoped MatrixGroups

theorem stmt5_2_8_U4_of_facts_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h526 : Stmt5_2_6_F4)
    (h527 : Stmt5_2_7_F4) (h312 : A312ForSQTK) (hExc : FactExcParabolicO2Ne)
    (hExcSq : FactExcParabolicO2NeSq) (hAut : AutA7Fact) : Stmt5_2_8_U4_F4 :=
  stmt5_2_8_U4_of_sl3_F4 h37 h38 h39 h526 h527 h312 hExc hExcSq hAut factSL3SmallModule_holds

end CFSG.Quasithin.H13
