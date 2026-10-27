module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBIface
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6StatementsS331

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

structure M22LemmasG_F4 : Prop where

  g64 : G64Out

  h612 : Stmt6_1_2_F4

  h616 : Stmt6_1_6_F4

  h6110 : Stmt6_1_10_F4

  h621 : Stmt6_2_1_F4

  h622 : Stmt6_2_2_F4

  h625 : Stmt6_2_5_F4

  h626 : Stmt6_2_6_F4

  h627 : Stmt6_2_7_F4

  h629 : Stmt6_2_9_F4

  h6210 : Stmt6_2_10_F4

  h6211 : Stmt6_2_11_F4

  h6212 : Stmt6_2_12_F4

section Data

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T M L V : Subgroup G}

theorem endN4_concl_F4 (hl : M22LemmasG_F4) (h : Hyp6Sec2 G T M L V)
    (hZS : ch6ZS T L V = V ⊓ UU T L V) : ∃ (g : G) (D : Subgroup G), EndN4Concl T L V g D := by
  obtain ⟨g, D, hk, h2, h3, h4, h5, h6, h7, h8⟩ := endN4_F4 hl.g64 hl.h621 hl.h622 hl.h626
    hl.h629 hl.h6210 hl.h6211 hl.h6212 hl.h6110 h hZS
  exact ⟨g, D, ⟨hk, hZS, h2, h3, h4, h5, h6, h7, h8⟩⟩

end Data

@[expose] def M22CaseBOne_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (g : G) (D : Subgroup G),
    M22LemmasG_F4 → Hyp6Sec2 G T M L V → EndN4Concl T L V g D →
      IsElemAbelian 2 (Subgroup.centralizer (V : Set G)) ∧
        V.relIndex (Subgroup.centralizer (V : Set G)) ≤ 2

@[expose] def M22CaseBTwo_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (g : G) (D : Subgroup G),
    M22LemmasG_F4 → Hyp6Sec2 G T M L V → EndN4Concl T L V g D →
      IsElemAbelian 2 (Subgroup.centralizer (V : Set G)) →
      V.relIndex (Subgroup.centralizer (V : Set G)) = 2 → False

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {g : G} {D : Subgroup G}

theorem centralizer_le_of_caseB_F4 (h1 : M22CaseBOne_F4) (h2 : M22CaseBTwo_F4) (hl : M22LemmasG_F4)
    (h : Hyp6Sec2 G T M L V) (hk : EndN4Concl T L V g D) :
    Subgroup.centralizer (V : Set G) ≤ V := by
  obtain ⟨hab, hle⟩ := h1 G T M L V g D hl h hk
  by_contra hne
  have hne1 : V.relIndex (Subgroup.centralizer (V : Set G)) ≠ 1 := fun h1 =>
    hne (Subgroup.relIndex_eq_one.mp h1)
  have hne0 : V.relIndex (Subgroup.centralizer (V : Set G)) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  exact h2 G T M L V g D hl h hk hab (by omega)

end CFSG.Quasithin.H13.GM22
