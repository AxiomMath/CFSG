module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Emb
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113F5113
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5112Eq
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2Cat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522Bot
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeC2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeEq
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeLt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalL2CatS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotJ2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotU4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522D42Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqCartanFour
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeEqThree

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.QTGen4.DSGen4

theorem stmt5_2_2_of_steps_F4
    (h515 : Stmt5_1_5_F4) (h516 : Stmt5_1_6_F4) (h510 : Stmt5_1_10_F4) (h5111 : Stmt5_1_11_F4)
    (h5113 : Stmt5_1_13C_F4) (h5114 : Stmt5_1_14_F4) (hU3 : FactU3Cover) (hRL : RankOneListedFacts.{0})
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hC58 : TheoremC58) (hDSB : DSBLoc_F4)
    (hDSC : DSCStatement_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_12_F4) (hc2 : Stmt5_2_2_ne_c2_conj)
    (h312c : Vol2Native.A312ForSQTKCat) (hF314 : A314Facts_F4) (hPar : Vol2.Ch11.SecA.FactL2Parabolic)
    (hTc : FactType513Aut) (hTp : FactType513Prime) : Stmt5_2_2C_F4 :=
  have hF5113 : FactF5113 := F5113.factF5113_holds
  have hL2 := stmt5_2_L2_of_F4 (stmt5_2_L2Gen_of_cat_F4 h510)
  have hcart := stmt5_2_2_eq_cartan_of_F4 h510 a38ForSQTKCat_holds
    (stmt5_2_2_eq_cartan_rank2_of_F4 h510 NQCat.factL2LieParabolic_holds hL2
      )
  have hLie := stmt5_2_L2Lie_of_inputs_cat_F4 hU3 hRL h515 h510
  have hD42 := stmt5_2_2_eq_D42_of_F4 h510 h331 hR NQCat.factL2LieParabolic_holds hLie
    Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds
  have hlist : Stmt5_2_2_bot_list_F4 := stmt5_2_2_bot_list_of_F4
    (stmt5_2_2_bot_D4_of_F4 h510 h331 hR hLie) (stmt5_2_2_bot_J2_of_F4 h510 h331 hR)
    (stmt5_2_2_bot_U4_of_F4 h510 h331 hR)
  stmt5_2_2_of_cat_F4 h515 h516 h510 h5111 h5113 h5114 hU3 hRL
    (stmt5_2_2_bot_of_F4 l2TorusFact (theorem311Stmt_of_C58 hC58) h510 h331 hR hL2 hLie
      hDSB hDSC hlist)
    (stmt5_2_2_ne_of_F4 l2TorusFact h510 h331 hR hL2 hLie
      (stmt5_2_2_ne_core_of_F4 h510 h331 hR h432
        (stmt5_2_2_ne_index_of_F4 h510 a38ForSQTKCat_holds NQCat.factL2LieParabolic_holds)
        (stmt5_2_2_ne_conj_of_F4 h510 h331 hR (theorem311Stmt_of_C58 hC58) h512
          Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds NQCat.factL2LieParabolic_holds
          (stmt5_2_2_ne_conj_c2_of_F4 h510 h331 hR h432 h515 h5113 Vol2Native.a37ForSQTKCat_proved
            a38ForSQTKCat_holds Vol2Native.a39ForSQTKCat_proved hc2))
        (stmt5_2_2_ne_lt_of_F4 h510 h331 hR h515 h5113 Vol2Native.a37ForSQTKCat_proved
          a38ForSQTKCat_holds Vol2Native.a39ForSQTKCat_proved)
        (stmt5_2_2_ne_eq_of_F4 h510 h331 hR NQCat.factL2LieParabolic_holds hLie
          Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds Vol2Native.a39ForSQTKCat_proved
          (stmt5_1_12_loc_of_F4 factMathieuOrders_holds hF314 a314NotLie2_holds hPar
            VolI.a36ForSQTK_holds (a312ForSQTK_of_cat h312c))
          (stmt5_1_13_loc_lie_of Vol2Native.a37ForSQTKCat_proved a38ForSQTKCat_holds hF5113)
          hD42 (stmt5_2_2_eq_three_of_F4 h510 h331 hR hL2 Vol2Native.a37ForSQTKCat_proved
            a38ForSQTKCat_holds Vol2Native.a36ForSQTKCat_proved hTc hTp hcart) hcart)))

end CFSG.Quasithin.H13
