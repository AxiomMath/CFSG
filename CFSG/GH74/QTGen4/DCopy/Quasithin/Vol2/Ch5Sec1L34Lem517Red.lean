module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem517
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34OddNoBlock
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34OddTIMp
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAmal
public import CFSG.Quasithin.Vol2.KGFactL34Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt5_1_17_of_reduced_F4
    (hI : L2OddInnerFact) (hL : L34SylowNormFact) (hF : L2TorusFact)
    (h515 : Stmt5_1_15_F4) (h516 : Stmt5_1_16_F4) (hIrr : IrrPlusBaseNonempty) (h323 : Stmt3_2_3)
    (h325 : Stmt3_2_5_F4) (h3228 : Stmt3_2_2_eight) (h513 : Stmt5_1_3_F4) (h5114 : Stmt5_1_14_first_F4)
    (h510 : Stmt5_1_10_F4) (hBor : L34BorelFact) (h517one : A5.Stmt5_1_7_one_F4)
    (h126 : A126TwoFact) (hmNine : Stmt5_1_17_mNine) : Stmt5_1_17_F4 :=
  stmt5_1_17_of_inputs_F4 hI hL hF h515 h516 hIrr h323 h325 h3228 h513 h5114 h510 hBor
    (stmt5_1_17_TI_of_F4 hI hF h5114 h517one) (stmt5_1_17_abelian_proved_F4 hI hF h5114 h126)
    (stmt5_1_17_amalgam_of hI hmNine l34AutTwoRankFact_holds)

end CFSG.Quasithin.H13
