module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtL1328Nat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L134W
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1344

public section

namespace CFSG.Quasithin.H13.U3

theorem stmt13_3_9_holds_of_F4
    (h1332 : Stmt13_3_2_F4)
    (h1226 : Stmt12_2_6_F4) (h1228 : Stmt12_2_8_F4) : A6.Stmt13_3_9_F4 :=
  stmt13_3_9_of_1332_F4 h1332 h1226 h1228 (stmt13_2_2_9L1_holds_F4 h1332)

theorem stmt13_4_4_holds_of_F4
    (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1226 : Stmt12_2_6_F4) (h1228 : Stmt12_2_8_F4) : Stmt13_4_4_F4 :=
  stmt13_4_4_of_F4 h1222 h1332 h1226 h1228 (stmt13_3_8_holds_F4 h1332) (stmt13_2_2_9L1_holds_F4 h1332)

end CFSG.Quasithin.H13.U3
