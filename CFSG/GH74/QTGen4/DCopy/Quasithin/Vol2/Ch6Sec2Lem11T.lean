module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11T
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem11P

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {d u₁ z : G}

theorem stmt6_2_11_of_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h6210 : Stmt6_2_10_F4) (hG31 : Ch6G31O2) :
    Stmt6_2_11_F4 := by
  intro G _ _ T M L V h
  show (V ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V)).relIndex V = 2
  by_contra h4
  obtain ⟨d, u₁, z, D⟩ := h.exists_data611_F4 h331 h432 h512 h614 h615 h6210 hG31 h4
  exact D.false

end CFSG.Quasithin.H13
