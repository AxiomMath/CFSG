module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13227
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3G2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt13_3_10_of_five_F4
    (h1332 : Stmt13_3_2_F4) (h1222 : Stmt12_2_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hC137 : C137StatementFive_F4) : Stmt13_3_10_F4 :=
  stmt13_3_10_of_c137_F4 h1332 h1222 h1334 (c137Statement_of_five_F4 hC137)
    (A6.stmt13_2_2_7_holds_F4 h1332 hC137)

end CFSG.Quasithin.H13.U3
