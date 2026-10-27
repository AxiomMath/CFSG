module

public import CFSG.Quasithin.Vol2.Ch6Skeleton
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Defs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6StatementsSec2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

theorem stmt6_2_19Sec2_of_F4 (h6213 : Stmt6_2_13_F4) (hcase2 : Stmt6_2_19Case2_F4) : Stmt6_2_19Sec2_F4 := by
  intro G _ _ T M L V h
  have hle : ch6ZS T L V ≤
      V ⊓ conjClosure (ch6ZS T L V)
        (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
    le_inf inf_le_left (le_conjClosure _ _)
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd hlt (hcase2 G T M L V h)
  · exact h6213 G T M L V h heq

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem stmt6_2_19_of_F4 (h6127 : Stmt6_1_27_F4) (hsec2 : Stmt6_2_19Sec2_F4) : Stmt6_2_19_F4 := by
  intro G _ _ T M L V n h
  obtain ⟨rfl, ⟨hnat, -⟩, hZS, -⟩ := h6127 G T M L V n h
  exact hsec2 G T M L ⁅V, L⁆ ⟨h.toNat hnat, hZS⟩

end CFSG.Quasithin.H13
