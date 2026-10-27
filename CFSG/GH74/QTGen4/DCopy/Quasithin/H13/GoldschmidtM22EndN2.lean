module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN1d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN2e

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

theorem endN2_F4 (hG : G64Out) (h621 : Stmt6_2_1_F4) (h622 : Stmt6_2_2_F4)
    (h626 : Stmt6_2_6_F4) (h629 : Stmt6_2_9_F4) (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4)
    (h6212 : Stmt6_2_12_F4) (h : Hyp6Sec2 G T M L V) (hZS : ch6ZS T L V = V ⊓ UU T L V) :
    Nonempty (PsiData T L V 3) := by
  obtain ⟨n, ψ, hn, hsurj, hker, hsn⟩ := endN1_F4 hG h622 h629 h6210 h6211 h hZS
  have hZ : Nat.card (quasithinOmegaOneCenter T) = 2 := (h622 G T M L V h).2.1
  let P : PsiData T L V n := ⟨ψ, hsurj, hker, hsn⟩
  rcases hn with rfl | hn
  · exact ⟨P⟩
  · exact (P.false_of_five_le_F4 h hZ h621 h626 h629 h6210 h6211 h6212 (by omega)).elim

end CFSG.Quasithin.H13.GM22
