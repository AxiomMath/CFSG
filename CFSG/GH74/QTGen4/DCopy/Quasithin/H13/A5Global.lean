module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Producer
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Top
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

theorem stmt13_6_1_of_inputs_F4
    (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h1323 : Input1323Two_F4) (h1336 : Input1336_F4)
    (h13515 : Input13515_F4) (h13518 : Input13518_F4) (h136 : Input136_F4)
    (hF431 : StmtF431U42) : Stmt13_6_1_F4 := by
  intro G _ _ T L h hA5
  obtain ⟨V, ⟨S⟩⟩ := exists_setting_F4 h132two h132fsu h132A5 h hA5
  exact S.thm_13_6_1_F4 h1323 h1336 h13515 h13518 h136 hF431

end CFSG.Quasithin.H13.A5
