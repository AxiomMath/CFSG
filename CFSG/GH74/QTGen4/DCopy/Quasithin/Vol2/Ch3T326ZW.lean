module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T326PP
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T326Z

public section
namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem caseD321_of_F4 (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (hG : T326ActsGlued_F4) (hD321 : D321Spelled)
    (hO2 : D321O2) : CaseD321_F4 := by
  intro G _ _ T L V₀ c _ _ hlt
  exact c.case_d321_F4 h316 hA37 hA38 hG hD321 hO2 hlt

theorem stmt3_2_6C_of_inputs_F4 (h331 : Stmt3_3_1_F4)
    (h3222 : Vol2.Ch10.TmpL6_3_2_2_two) (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight)
    (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (hD37 : D37) (hD36 : D36c) (hL38 : D3L38)
    (hB48 : D36B48q) (h6 : Vol2.Ch11.TmpL6_3_2_2_six_F4) (hG : T326ActsGlued_F4)
    (hD321 : D321Spelled) (hO2 : D321O2) : Stmt3_2_6C_F4 :=
  stmt3_2_6C_of_cases_F4 h331 h3222 h3228 h316 hA37 hA38 hD37 hD36 hL38 hB48 h6 hG
    (caseD321_of_F4 h316 hA37 hA38 hG hD321 hO2)

end CFSG.Quasithin.H13.T326
