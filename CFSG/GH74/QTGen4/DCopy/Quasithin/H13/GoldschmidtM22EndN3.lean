module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN3e

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

theorem endN3_F4 (hG : G64Out) (h621 : Stmt6_2_1_F4) (h622 : Stmt6_2_2_F4)
    (h626 : Stmt6_2_6_F4) (h629 : Stmt6_2_9_F4) (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4)
    (h6212 : Stmt6_2_12_F4) (h : Hyp6Sec2 G T M L V) (hZS : ch6ZS T L V = V ⊓ UU T L V) :
    ∃ (g : G) (D : Subgroup G), KData T L V g D := by
  obtain ⟨P⟩ := endN2_F4 hG h621 h622 h626 h629 h6210 h6211 h6212 h hZS
  exact P.kData_F4 h (h622 G T M L V h).2.1 h621 h626 h6210 h6211 h6212

end CFSG.Quasithin.H13.GM22
