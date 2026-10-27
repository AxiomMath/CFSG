module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A58e

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Contra14_5_3Solv_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ Y : Subgroup G), Ctx_F4 G T L V V₂ Y →
    pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ → Group.IsSolvable ↥(hY T L V₂ Y) → False

theorem contra14_5_3_of_F4 (hS : Contra14_5_3Solv_F4) (h4 : Lemma14_7_4_two_three_F4)
    (h55 : Lemma14_5_5Q_F4) (h36 : A36ForSQTK) (h1434 : Lemma1434One_F4) (hSym : Lemma14_5_8Sym_F4) :
    Contra14_5_3_F4 := by
  intro G _ _ T L V V₂ Y C
  exact hS G T L V V₂ Y C (lemma14_5_5_of_F4 h55 h4 G T L V V₂ Y C)
    (C.isSolvable_hY_F4 h4 h55 h36 h1434 hSym)

theorem thm14_5_3_of_solv_F4 (hS : Contra14_5_3Solv_F4) (h4 : Lemma14_7_4_two_three_F4)
    (h55 : Lemma14_5_5Q_F4) (h36 : A36ForSQTK) (h1434 : Lemma1434One_F4) (hSym : Lemma14_5_8Sym_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Thm14_5_3_F4 :=
  thm14_5_3_of_F4 (contra14_5_3_of_F4 hS h4 h55 h36 h1434 hSym) h1222 h1332 h1334

end CFSG.Quasithin.H13.L32A.T53
