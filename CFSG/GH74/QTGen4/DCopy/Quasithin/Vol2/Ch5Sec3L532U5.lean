module

public import CFSG.Quasithin.Vol2.Ch5Sec3L532U5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L532Ext
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

theorem stmt5_3_2At_u5_F4
    (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4) : Stmt5_3_2At_F4 .PSU 5 :=
  stmt5_3_2At_of_modelAt_F4 h527 h531 modelAt_u5

end CFSG.Quasithin.H13.L532
