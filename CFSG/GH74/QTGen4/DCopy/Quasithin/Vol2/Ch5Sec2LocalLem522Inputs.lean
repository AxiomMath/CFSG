module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2Two
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt5_2_2_of_inputs_F4
    (h515 : Stmt5_1_5_F4) (h516 : Stmt5_1_6_F4) (h510 : Stmt5_1_10_F4) (h5111 : Stmt5_1_11_F4)
    (h5113 : Stmt5_1_13C_F4) (h5114 : Stmt5_1_14_F4) (hU3 : FactU3Cover) (hF : FactL2LieParabolic)
    (hRL : RankOneListedFacts.{0}) (hbot : Stmt5_2_2_bot_F4) (hne : Stmt5_2_2_ne_F4) : Stmt5_2_2C_F4 :=
  stmt5_2_2_of_F4 Vol2Native.a39ForSQTKCat_proved h510 h516 h5113 h5114
    (stmt5_2_1_of_F4 h510 h5111 (stmt5_2_1_par_of_inputs_F4 hU3 hF hRL h515 h510)) l2TorusFact
    (ch5L2ChoiceExists_of_inputs_F4 h510 hF) hbot hne

end CFSG.Quasithin.H13
