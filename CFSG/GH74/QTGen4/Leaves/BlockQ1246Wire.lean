module

public import CFSG.GH74.QTGen4.Leaves.BlockQ1246Gen4
public import CFSG.Quasithin.Vol2.Ch12Sec4N6Core
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4N6Ctx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4N6Q

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative Pointwise commutatorElement

theorem blockQ1246SL27_of_gen4_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9_F4) (h51 : AsB51) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : BlockQ1246SL27_F4 := by
  intro G _ _ T L V hcx h3 E hEV hE4 hTE hN hcomm hO2
  obtain ⟨z, v, _, c⟩ := N1246.exists_ctx_F4 h331 h1222 hpre h3228 h1229 h51 h37 h38 h39 hcx h3 hEV
    hE4 hTE
  exact c.Q_eq_of_comm hcomm (c.comm_of_gen4 (CFSG.GH74.QTGen4.Finite4.gen4 (G := G)) hcomm)

end CFSG.Quasithin.H13
