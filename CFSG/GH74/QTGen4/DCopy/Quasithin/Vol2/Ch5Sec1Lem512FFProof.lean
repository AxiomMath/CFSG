module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512FFProof

public section
namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem stmt5_1_2_of_asB51_F4 (h331 : Stmt3_3_1_F4) (h51 : AsB51) : Stmt5_1_2_F4 :=
  stmt5_1_2_of_F4 h331 (stmt5_1_2_FF_of_asB51 h51)

end CFSG.Quasithin.H13
