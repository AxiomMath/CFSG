module

public import CFSG.GH74.QTGen4.Leaves.L14742
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk6

public section

namespace CFSG.GH74.QTGen4.Leaves.L14742

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.GH74 CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A.C

theorem lemma14_7_46_F4_holds
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4) (h1222 : Stmt12_2_2_F4) :
    Lemma14_7_46_F4 := by
  intro G _ _ T L V H S K hK _ n hn hLie
  exact (false_of_setting147_lieChar2 CFSG.GH74.QTGen4.Finite4.gen4
    (S.hypF98_F4 h13322 hMod h1222) S.hz.2.1 S.hyp.abelian (fun x hx => le_of_mem_cComp hK hx)
    (by omega) hLie).elim

end CFSG.GH74.QTGen4.Leaves.L14742
