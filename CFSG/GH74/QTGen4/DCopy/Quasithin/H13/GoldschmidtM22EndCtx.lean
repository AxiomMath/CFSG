module

public import CFSG.Quasithin.H13.GoldschmidtM22EndCtx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6StatementsSec2

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

section Parts

variable (h : Hyp6Sec2 G T M L V)
include h

theorem UU_le_pCore_F4 (h6210 : Stmt6_2_10_F4) : UU T L V ≤ pCoreOf 2 (HH T) :=
  (h6210 G T M L V h).1.2.1

theorem commutator_UU_le_F4 (h6210 : Stmt6_2_10_F4) :
    ⁅UU T L V, pCoreOf 2 (HH T)⁆ ≤ quasithinOmegaOneCenter T :=
  (h6210 G T M L V h).1.2.2

theorem CHU_le_normalizer_V_F4 (h6210 : Stmt6_2_10_F4) :
    CHU T L V ≤ Subgroup.normalizer (V : Set G) :=
  (h6210 G T M L V h).2.1.1

theorem isO2Trivial_CHU_F4 (h6210 : Stmt6_2_10_F4) : IsO2Trivial (HH T) (CHU T L V) :=
  (h6210 G T M L V h).2.2.1

theorem not_V_le_CHU_F4 (h6210 : Stmt6_2_10_F4) : ¬ V ≤ CHU T L V :=
  (h6210 G T M L V h).2.2.2.1

theorem commutator_V_UU_le_F4 (h6210 : Stmt6_2_10_F4) : ⁅V, UU T L V⁆ ≤ V ⊓ UU T L V :=
  (h6210 G T M L V h).2.2.2.2

theorem relIndex_V_CHU_F4 (h6211 : Stmt6_2_11_F4) : (V ⊓ CHU T L V).relIndex V = 2 :=
  h6211 G T M L V h

theorem HH_inf_normalizer_ZS_le_F4 (h629 : Stmt6_2_9_F4) :
    HH T ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
  (h629 G T M L V h).2.1.symm.le.trans inf_le_right

end Parts

end CFSG.Quasithin.H13.GM22
