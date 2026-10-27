module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.FiveQuotients
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L1332Wired
public import CFSG.Quasithin.H13.L32NoIrrFourProof
public import CFSG.Quasithin.H13.LocDblSporadic
public import CFSG.Quasithin.Vol2.GoldschmidtTD32

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt13_3_2_of_frontier_F4
    (h137 : Stmt13_1_7_F4) (h1222 : Stmt12_2_2_F4) (h1242 : Stmt12_4_2_F4) (h1271 : Stmt12_7_1_F4)
    (hA7 : StmtFiveA7Elim_F4) (hLin : LinearSelectedNaturalConfigurationProducer_F4) : Stmt13_3_2_F4 :=
  stmt13_3_2_of_open_F4 LocDbl.local_double_embedding_exclusion h137
    (stmt13_1_2_three_of_inputs_F4 h1222 hA7 hLin) stmt3_2_3_proved h1222 h1242 h1271
    l32NoIrrFour_holds

end CFSG.Quasithin.H13
