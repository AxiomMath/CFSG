module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L134K
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L139S

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem stmt13_3_8_holds_F4
    (h1332 : Stmt13_3_2_F4) : A6.Stmt13_3_8_F4 :=
  stmt13_3_8_of_F4 h1332 (stmt13_3_4K_of_F4 h1332)

theorem stmt13_3_9_of_1332_F4
    (h1332 : Stmt13_3_2_F4) (h1226 : Stmt12_2_6_F4)
    (h1228 : Stmt12_2_8_F4) (hL1 : Stmt13_2_2_9L1_F4) : A6.Stmt13_3_9_F4 :=
  stmt13_3_9_of_F4 h1332 h1226 h1228 (stmt13_3_8_holds_F4 h1332) hL1

end CFSG.Quasithin.H13.U3
