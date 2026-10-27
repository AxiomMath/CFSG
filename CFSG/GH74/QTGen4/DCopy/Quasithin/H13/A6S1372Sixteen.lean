module

public import CFSG.Quasithin.H13.A6S1372Sixteen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372FifteenB

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}
  {H : Subgroup G}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem exists_KData_F4
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) (h56 : AsB56) (h51 : AsB51) (h42 : AsB42)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ B K, C.KData B K := by
  obtain ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ, hB4, h15⟩ :=
    C.exists_K_b42_F4 hNS h13315 h1356two hH hab hhat hNU hna h13314 hLem h56 h51 h42
  exact ⟨B, K, hB, hBA, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ, hB4, h15,
    S.pCoreOf_plus_eq_bot_F4 hNS h13315 h1356two hH hab hNU hhat hLem⟩

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
