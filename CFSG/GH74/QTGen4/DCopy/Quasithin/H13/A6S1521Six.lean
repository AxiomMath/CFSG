module

public import CFSG.Quasithin.H13.A6S1521Six
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1522

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

theorem input13521Six_of_comm_F4
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (h38 : A38ForSQTK)
    (hF : A5.Facts1321) (hR : A5.FactRankRows1321) (hA7 : A5.FactA7Grp1321)
    (hL3 : A5.FactL3Grp1321) (hO : A5.FactOutRows1321) (hC : FactCommRows1321) :
    Input13521Six_F4 := by
  intro G _ _ T L V S hNS _ hcon H hH hna
  have hVH : V ≤ H := (S.toA5Sit_F4 hNS h13315 h1356two hH hna).V_le_H
  refine comm_L1_eq_of_commSubOf (S.toA5Sit_F4 hNS h13315 h1356two hH hna) ?_
  by_cases hhat : IsHatA6 L
  · exact commSubOf_L1_eq_top_of_rows (S.toA5Sit_F4 hNS h13315 h1356two hH hna) VolI.stmtF956i h38
      (S.toA5SitY_L0_F4 hNS h13315 h1356two hH hna hhat) (S.lemma13_5_19_two_l0 hhat hVH)
      (fun _ hl => S.cube_mem_pCoreOf_L1_hat hhat hl) hF hR hA7 hL3 hO hC
  · exact commSubOf_L1_eq_top_of_rows (S.toA5Sit_F4 hNS h13315 h1356two hH hna) VolI.stmtF956i h38
      (S.toA5SitY_F4 hNS h13315 h1356two hH hna hhat)
      (S.lemma13_5_19_two_L1_F4 hNS h13315 h1356two (hcon hhat) hH)
      (fun _ hl => S.cube_mem_pCoreOf_L1 hhat hl) hF hR hA7 hL3 hO hC

end CFSG.Quasithin.H13.A6
