module

public import CFSG.Quasithin.H13.GoldschmidtM22G64B56
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseA3Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBTwo
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem10
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem11T
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem12
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem5H
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Remark612
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBOne

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.Quasithin.ASInputs

theorem stmt6_2_13_of_F4 (hKu : StmtKuM22_F4) (h56 : AsB56) (h311 : Theorem311Stmt) (h331 : Stmt3_3_1_F4)
    (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4) (h513 : Stmt5_1_3_F4) (h614 : Stmt6_1_4_F4)
    (h615 : Stmt6_1_5_F4) (hE63 : Ch6InE63) (hE612 : Ch6InE612) (hRes : Res627FF) (hF : F713Two)
    (hL : Res628Lie) (hG31 : Ch6G31O2) : Stmt6_2_13_F4 := by
  have h6110 := stmt6_1_10_F4 h311 h432 hE63
  have h6210 := (stmt6_2_8_and_10_of_res_F4 h331 h432 h512 h614 h615 h6110 hE612 hRes hF hL).2
  have h6211 := stmt6_2_11_of_F4 h331 h432 h512 h614 h615 h6210 hG31
  exact GM22.stmt6_2_13_of_F4 hKu GM22.m22CaseBOne_holds_F4 GM22.m22CaseBTwo_holds_F4
    GM22.m22CaseAThree_holds_F4
    ⟨GM22.g64Out_of_b56 h56, stmt6_1_2_F4 h512 h513, stmt6_1_6_F4 h331 h432 h512 h614 h615, h6110,
      stmt6_2_1_F4 h432, stmt6_2_2_F4 h331 h432 h512 h614 h615, stmt6_2_5_of_F4 h331 h432 h615 h6110 hE612,
      stmt6_2_6_of_F4 h331 h432 h615 h6110 hE612, stmt6_2_7_of_res_F4 h331 h432 h615 h6110 hE612 hRes,
      stmt6_2_9_F4 h331 h432 h512 h614 h615, h6210, h6211, stmt6_2_12_of_F4 h331 h432 h512 h614 h615 h6211⟩

end CFSG.Quasithin.H13
