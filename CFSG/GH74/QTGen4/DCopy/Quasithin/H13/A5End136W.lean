module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Close1321c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L134W

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Quasithin

theorem end136_of_1332_F4
    (h1323 : Input1323Two_F4) (h1336 : Input1336_F4) (h1332 : Stmt13_3_2_F4) (hfin : Fin136_F4) :
    End136_F4 :=
  end136_of_fin_F4 h1323 h1336 (U3.stmt13_3_8_holds_F4 h1332) hfin

theorem input136_of_1332_F4
    (h137 : Thm13_6_7_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4) (h1323 : Input1323Two_F4)
    (h1332 : Stmt13_3_2_F4) (hfin : Fin136_F4) : Input136_F4 :=
  input136_of_F4 h137 h1326 h1336 (end136_of_1332_F4 h1323 h1336 h1332 hfin)

end CFSG.Quasithin.H13.A5
