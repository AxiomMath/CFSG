module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem16Two
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem17
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem18
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem18Rank

public section

namespace CFSG.Quasithin.H13

theorem stmt12_2_18_of_A8Zv_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (hzv : Lem12216A8Zv_F4)
    (h1227 : Stmt12_2_7_F4) : Stmt12_2_18_F4 :=
  stmt12_2_18_of_F4 h331 h1222 h323 (stmt12_2_16_of_A8Zv_F4 h1222 h331 h323 hzv)
    (stmt12_2_17_of_F4 (stmt12_2_16_of_A8Zv_F4 h1222 h331 h323 hzv) h1222 h323)
    (lem12218TwoRank_of_F4 h331 h1222 h323 h1227)

end CFSG.Quasithin.H13
