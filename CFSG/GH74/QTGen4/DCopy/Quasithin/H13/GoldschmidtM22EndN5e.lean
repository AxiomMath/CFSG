module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN3a

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include P h in

theorem CHU_le_T_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1_F4)
    (h629 : Stmt6_2_9_F4) (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) : CHU T L V ≤ T := by
  intro x hx
  have : x ∈ HH T ⊓ M :=
    ⟨centralizerMod_le_left _ _ _ hx, (h621 G T M L V h).2 (CHU_le_normalizer_V_F4 h h6210 hx)⟩
  rwa [P.HH_inf_M_eq_T_F4 h hZ h629 h6210 h6212] at this

end PsiData

end CFSG.Quasithin.H13.GM22
