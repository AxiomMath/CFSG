module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem19
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Prop27Three
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem19Top
public import CFSG.GH74.QTGen4.Leaves.Ch12.Config1224F4
public import CFSG.GH74.QTGen4.Leaves.Ch12.Lem12222Gen4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem25I
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem25J
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem18RankTop
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20TrB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem21
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem21Post
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem24

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13

theorem stmt12_2_13_F4_of_inputs
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (h325 : Stmt3_2_5_F4)
    (hI62 : CFSG.Quasithin.ASInputs.AS_I_6_2_twoCases) (hzv : Lem12216A8Zv_F4) (h1227 : Stmt12_2_7_F4)
    (hsplit : Lem12226Split_F4) (hAsc : Asc94_M24He_L52Type_F4)
    (hM12 : CFSG.GH74.M12.S_Asc03_Theorem1) : Stmt12_2_13_F4 := by
  have h1216 := stmt12_2_16_of_A8Zv_F4 h1222 h331 h323 hzv
  have h12218 := stmt12_2_18_of_A8Zv_F4 h331 h1222 h323 hzv h1227
  have hpick := lem12220PickFull_of_coprime_F4 h331 h1222 h325 h1216 h12218 hI62
  have h2123 := lem12221_23_of_F4 hpick (lem12221_of_F4 h331 h1222)
    (lem12222_of_F4 h331 h1222 h325 h1216 h12218 hI62 lem12222Frattini_F4_holds)
    (lem12223_of_F4 h331 h1222 lem12222Frattini_F4_holds) (lem12223Post_of_F4 h1222)
  have hsol := lem12219Solvable_of_F4 h331 h1222 h1216 h12218 h1227
  have h1220 := stmt12_2_20_of_solv_F4 h1222 h323 hsol (lem12220Pick_of_full_F4 hpick)
    (lem12220Transv_of_F4 h1222)
  exact stmt12_2_13_of_config_F4
    (stmt12_2_24_config_of_solv_F4 hsol h1220 h2123 (lem12224Block_of_F4 h1222))
    (stmt12_2_25_26_of_config_F4_of_inputs h331 h1222 h323 h1216 h1220 hsplit)
    (stmt12_2_27_of_F4 hAsc hM12 (stmt12_2_6_of_F4 h1222 h323))

theorem lem12226Split_F4_of_inputs
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16_F4) (h1220 : Stmt12_2_20_F4) : Lem12226Split_F4 := by
  intro G _ _ T L V H P U I h n p hH hNE hC
  exact Lem25.exists_complement_of_three_F4 h1222 hH hC
    (Lem25.prime_eq_three_of_three_F4 h331 h1222 h323 h1216 h1220 hH hNE hC
      (n_eq_three_of_config_gen4 hC).1)

theorem stmt12_2_13_F4_of_basic_inputs
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (h325 : Stmt3_2_5_F4)
    (hI62 : CFSG.Quasithin.ASInputs.AS_I_6_2_twoCases) (hzv : Lem12216A8Zv_F4)
    (h1227 : Stmt12_2_7_F4) (hAsc : Asc94_M24He_L52Type_F4)
    (hM12 : CFSG.GH74.M12.S_Asc03_Theorem1) : Stmt12_2_13_F4 := by
  have h1216 := stmt12_2_16_of_A8Zv_F4 h1222 h331 h323 hzv
  have h12218 := stmt12_2_18_of_A8Zv_F4 h331 h1222 h323 hzv h1227
  exact stmt12_2_13_F4_of_inputs h331 h1222 h323 h325 hI62 hzv h1227
    (lem12226Split_F4_of_inputs h331 h1222 h323 h1216
      (stmt12_2_20_of_solv_F4 h1222 h323 (lem12219Solvable_of_F4 h331 h1222 h1216 h12218 h1227)
        (lem12220Pick_of_full_F4
          (lem12220PickFull_of_coprime_F4 h331 h1222 h325 h1216 h12218 hI62))
        (lem12220Transv_of_F4 h1222)))
    hAsc hM12

end CFSG.GH74.QTGen4.Leaves
