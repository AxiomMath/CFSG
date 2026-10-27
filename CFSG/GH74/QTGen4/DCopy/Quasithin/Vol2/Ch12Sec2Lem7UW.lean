module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem7Lists
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem7U
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.H13.NQCatLemma128One
public import CFSG.Quasithin.Vol2.GoldschmidtTD32

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt12_2_7_of_unique_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h6220 : Stmt6_2_20_F4) (h37 : A37ForSQTK)
    (h3214 : Stmt3_2_14_F4) : Stmt12_2_7_F4 :=
  stmt12_2_7_of_lists_F4 h331 h1222 stmt3_2_3_proved h6220 e22StatementNoN_proved h37
    NQCat.lemma128One_holds (lem1227NotQuasisimple_of_unique_F4 h331 h3214)

end CFSG.Quasithin.H13
