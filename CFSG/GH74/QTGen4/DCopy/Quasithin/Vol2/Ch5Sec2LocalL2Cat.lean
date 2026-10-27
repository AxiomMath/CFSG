module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522Inputs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.H13.NQCatL2LieParabolic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt5_2_2_of_cat_F4
    (h515 : Stmt5_1_5_F4) (h516 : Stmt5_1_6_F4) (h510 : Stmt5_1_10_F4) (h5111 : Stmt5_1_11_F4)
    (h5113 : Stmt5_1_13C_F4) (h5114 : Stmt5_1_14_F4) (hU3 : FactU3Cover) (hRL : RankOneListedFacts.{0})
    (hbot : Stmt5_2_2_bot_F4) (hne : Stmt5_2_2_ne_F4) : Stmt5_2_2C_F4 :=
  stmt5_2_2_of_inputs_F4 h515 h516 h510 h5111 h5113 h5114 hU3 NQCat.factL2LieParabolic_holds hRL
    hbot hne

end CFSG.Quasithin.H13
