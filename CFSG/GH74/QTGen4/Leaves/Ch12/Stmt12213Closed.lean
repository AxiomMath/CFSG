module

public import CFSG.GH74.QTGen4.Leaves.Ch12.Stmt12213F4
public import CFSG.Quasithin.Vol2.GoldschmidtTD32
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.GH74.M12.AscTheorem1
public import CFSG.GH74.QTGen4.DCopy.Roots.Cuts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem26A8Fix

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13

theorem stmt12_2_13_F4_of_stmts
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h325 : Stmt3_2_5_F4) (h1227 : Stmt12_2_7_F4) :
    Stmt12_2_13_F4 :=
  stmt12_2_13_F4_of_basic_inputs h331 h1222 stmt3_2_3_proved h325
    CFSG.Quasithin.I62.as_I_6_2_twoCases_holds
    (lem12216A8Zv_holds_F4 h1222 stmt3_2_3_proved stmt3_2_2_eight_proved
      CFSG.Quasithin.B5.asB51_holds)
    h1227 CFSG.GH74.QTGen4.DCopy.Roots.asc94_M24He_L52Type_F4_holds
    CFSG.GH74.M12.s_asc03_theorem1

end CFSG.GH74.QTGen4.Leaves
