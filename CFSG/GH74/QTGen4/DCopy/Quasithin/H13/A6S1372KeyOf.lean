module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372Key
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372KeyData
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L24c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372Sixteen

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem key13721_of_F4
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (h13314 : Stmt13_3_14_F4)
    (hLem : Lem1374One_F4) (h56 : AsB56) (h51 : AsB51) (h42 : AsB42) (h1352 : Stmt13_5_2_F4)
    (hAlt : Lem1376AltNat_F4) (h13719 : Lem13719L1K_F4) : Key13721_F4 := by
  intro G _ _ T L V S hNS hNU hhat hG1 hab hna
  have : IsMulCommutative ↥(conjClosure S.V3 S.G1) := hab.1
  obtain ⟨C⟩ := S.exists_conf_F4 hNS h13315 h1356two hG1 hab hna
  obtain ⟨B, K, hK⟩ :=
    C.exists_KData_F4 hNS h13315 h1356two hG1 hab hhat hNU hna h13314 hLem h56 h51 h42
  exact ⟨K, hK.2.2.1, hK.key_data_F4 hNS h13315 h1356two hG1 hhat hNU hna h13314 hLem h1352 h51
    hAlt hab (hK.not_L24_F4 hNS h13315 h1356two hG1 hhat hNU hna h13314 hLem h1352 h51 h13719 hab)⟩

end CFSG.Quasithin.H13.A6
