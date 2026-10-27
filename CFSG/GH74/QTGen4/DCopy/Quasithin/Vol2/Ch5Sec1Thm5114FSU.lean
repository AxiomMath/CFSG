module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114FSU
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Thm5114Max

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem exists_fsu_F4
    (h510 : Stmt5_1_10_F4) (h5112 : Stmt5_1_12_F4) (h323 : Stmt3_2_3)
    (hKf : quasithinIsFaithfulLocal T (oTwoUpper H)) :
    ∃ V₀ : Subgroup G,
      IsIrrPlusIn (oTwoUpper H) (reducedAggregate (oTwoUpper H ⊔ T)) T V₀ ∧
        FSU G T (oTwoUpper H) V₀ := by
  have hmax := isMaximalLocal_of_L34_F4 h510 h5112 h.hyp h.notation59 h.l34
  obtain ⟨-, -, hI⟩ := h323 G T (oTwoUpper H) h.hyp.simple h.hyp.nonabelian h.hyp.qtke
    h.hyp.sylow hmax hKf h.isQuasisimple_K
  rw [h.conjClosure_K] at hI
  obtain ⟨I, hIb⟩ := h.exists_irrPlusBase_K hKf
  obtain ⟨V₀, hV₀, -, hfsu⟩ := hI I hIb
  exact ⟨V₀, hV₀, hfsu⟩

end Hyp5_1_14

end CFSG.Quasithin.H13
