module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BAlt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Ch1Four

theorem alt_a_of_amalgam_F4 (h526 : Stmt5_2_6_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T M L V H B D L₂ : Subgroup G} {n : ℕ} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hα : IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSL 3 n) ∨
      IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSp 2 n)) :
    L₂ = oTwoUpper H ∧ sec52S M H ≤ L ∧ sec52S M H ≤ oTwoUpper H ∧
      pCoreOf 2 (oTwoUpper H ⊔ T) = pCoreOf 2 (oTwoUpper H) ∧
      sec52AlphaPrime M L H B D = sec52Alpha M L H B D L₂ := by
  obtain ⟨-, hL₂K, -, -, -, -, hKT, halt⟩ := h526 G T M L V H B D L₂ n hyp
  rcases halt with ⟨hSL, hSK, -, hKS⟩ | ⟨m, hnm, -, hU4, -⟩
  · refine ⟨hL₂K, hSL, hSK, hKT.trans hKS, ?_⟩
    simp only [sec52AlphaPrime, sec52Alpha, sec52G1, sec52G2, inf_eq_left.mpr hSL, hL₂K]
  · exact absurd hU4 (not_isU4ExtTwo hnm hα)

end CFSG.Quasithin.H13
