module

public import CFSG.Quasithin.H13.GoldschmidtL1328Nat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6HatPlusB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtL1329Five

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

theorem stmt13_2_2_9L1Nat_holds_F4 (h1332 : Stmt13_3_2_F4) :
    Stmt13_2_2_9L1Nat_F4 := by
  intro G _ _ T L V hH hV _ hhat hZV
  obtain ⟨S⟩ := exists_setting4_of_1332_F4 h1332 hH hhat.2.2 hV hZV
  exact L1328.normalizer_L1_le_of_hat S hhat

theorem stmt13_2_2_9L1_holds_F4 (h1332 : Stmt13_3_2_F4) :
    Stmt13_2_2_9L1_F4 :=
  stmt13_2_2_9L1_of_cases_F4 (stmt13_2_2_9L1Nat_holds_F4 h1332) (stmt13_2_2_9L1Perm_holds_F4 h1332)

end CFSG.Quasithin.H13.U3
