module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T326GD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3T326ZW
public import CFSG.Quasithin.Vol2.Ch3T326GB

public section
namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SmithD321
open scoped IsMulCommutative

theorem t326ActsGlued_of_F4 (h331 : Stmt3_3_1_F4)
    (h3222 : Vol2.Ch10.TmpL6_3_2_2_two) (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight)
    (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (h6 : Vol2.Ch11.TmpL6_3_2_2_six_F4) (hD321 : D321Spelled)
    (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42) (h36 : D36c) (h37 : D37)
    (hB56 : AsB56) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hL38 : D3L38) : T326ActsGlued_F4 := by
  intro G _ _ T L V₀ hfsu hne _ t ht htn h1 h2 h3 hnd
  have c := Ctx.of_F4 h331 h3222 h3228 hfsu hne
  have := c.elemV.1
  by_cases hV : conjClosure V₀ T =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
  · refine c.qhatStar_acts_of_eq_F4 h316 h6 hV fun hC => hnd ?_
    rw [hC, sup_bot_eq] at h1
    rw [hC, sup_bot_eq, sup_bot_eq] at h2
    exact ⟨h1, h2⟩
  · exact c.qhatStar_acts_of_lt h316 hA37 hA38 hD321 hA21 hB42 h9 h36 h37 hB56 h38 hA23 hSzF
      hL38 hV

theorem stmt3_2_6C_of_inputs'_F4 (h331 : Stmt3_3_1_F4)
    (h3222 : Vol2.Ch10.TmpL6_3_2_2_two) (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight)
    (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (hD37 : D37) (hD36 : D36c) (hL38 : D3L38)
    (hB48 : D36B48q) (h6 : Vol2.Ch11.TmpL6_3_2_2_six_F4) (hD321 : D321Spelled) (hO2 : D321O2)
    (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42) (hB56 : AsB56) (h38 : D38Top)
    (hA23 : A23SQTKListFact) (hSzF : H13.SimpleThreePrimeSuzukiFact) : Stmt3_2_6C_F4 :=
  stmt3_2_6C_of_inputs_F4 h331 h3222 h3228 h316 hA37 hA38 hD37 hD36 hL38 hB48 h6
    (t326ActsGlued_of_F4 h331 h3222 h3228 h316 hA37 hA38 h6 hD321 hA21 hB42 h9 hD36 hD37 hB56 h38
      hA23 hSzF hL38) hD321 hO2

end CFSG.Quasithin.H13.T326
