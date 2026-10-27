module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518D5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518DLO
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.QTGen4.DSGen4

theorem stmt5_1_18_D5_of_F4 (hDSC : DSCStatement_F4)
    (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4) (h510 : Stmt5_1_10_F4) (h516 : Stmt5_1_16_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts_F4)
    (hFive : A314FiveNormFact) : Stmt5_1_18_D5_F4 :=
  stmt5_1_18_D5_of_inputs_F4 l34TwoParabolicFact l34TwoAutFact l2TorusFact h311 h5114 h510 h516 h331
    hR hDSC h36 h37 h38 h39 h312 h314 hFive

theorem stmt5_1_18_of_f112_F4 (hDSA : DSALoc_F4)
    (hDSC : DSCStatement_F4)
    (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first_F4) (h432 : Stmt4_3_2_F4) (h510 : Stmt5_1_10_F4)
    (h515 : Stmt5_1_15_F4) (h516 : Stmt5_1_16_F4) (h517 : Stmt5_1_17_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) (hPC : L34ParabolicChiefFact)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h314 : A314Facts_F4) (hFive : A314FiveNormFact) : Stmt5_1_18_F4 :=
  stmt5_1_18_of_reduced_outer_F4 l2TorusFact h510 h515 h516 h5114 h517 h432 h331 hR
    hDSA hPC
    (stmt5_1_18_D5_of_F4 hDSC h311 h5114 h510 h516 h331 hR h36 h37 h38 h39 h312 h314 hFive)

end CFSG.Quasithin.H13
