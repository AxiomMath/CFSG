module

public import CFSG.Quasithin.H13.A5S1525
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1519
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1522
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5SitBridge5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Top

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Blueprint

theorem input13518_of_F4
    (h1323 : Input1323Two_F4) (h1326 : Input1326Two_F4) (h1336 : Input1336_F4)
    (hF956 : StmtF956i) (h38 : A38ForSQTK) (hF : Facts1321) (hR : FactRankRows1321)
    (hA7 : FactA7Grp1321) (hL3 : FactL3Grp1321) (hO : FactOutRows1321)
    (hQ : FactQuadRows1321) : Input13518_F4 := by
  intro G _ _ T L V S hna
  by_contra hcon
  push Not at hcon
  have hH := S.G1_mem_Hz_F4 h1336
  obtain ⟨u, hu, huc, hu2⟩ := (S.toA5Sit_F4 h1323 h1326 h1336 hH hna).exists_comm_sq_ne_one hF956
    h38 (S.toA5SitY_F4 h1323 h1326 h1336 hH hna) (S.lemma_13_5_19_two_F4 h1323 hcon hH)
    (fun _ hl => S.cube_mem_pCoreOf_L1 hl) hF hR hA7 hL3 hO hQ S.cL1_mem S.cL1_cube
    S.cL1_not_mem_Q
  exact hu2 (S.sq_eq_one_of_comm_cL1_F4 h1323 hH hna hu huc)

end CFSG.Quasithin.H13.A5
