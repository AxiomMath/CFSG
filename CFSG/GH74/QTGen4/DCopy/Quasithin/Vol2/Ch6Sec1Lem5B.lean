module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5BS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

theorem Hyp611.cx615_F4 (h614 : Stmt6_1_4_F4) (h : Hyp611 G T M L V n) (hH : IsHStar T M H)
    (hZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    Cx615 G T M L (reducedAggregate (L ⊔ T)) H n :=
  ⟨h.reduced_ch615_F4 h614, hH, hZ, h.omega_le_reduced_ch615⟩

namespace Cx615

variable (c : Cx615 G T M L V H n)
include c

theorem thompsonJ_not_le_F4 (h331 : Stmt3_3_1_F4) (h5172 : Stmt5_1_7_two_F4) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (UH T H : Set G) := by
  have hMP := c.minParabolic_F4 h331
  have hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro hb
    apply c.notZ
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
    exact hb
  obtain ⟨-, hKeq, -⟩ := h5172 G T M L V H n c.hyp.toHyp5_0_1 c.hyp.module c.hH hZH
  have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  intro hJC
  have hJO : thompsonJ T ≤ pCoreOf 2 H := by
    rw [← hMP.inf_centralizer_eq_pCoreOf c.UH_red.2 c.not_le_centralizer_UH]
    exact le_inf hJT hJC
  have hii := hMP.commutator_lt_iff_le_pCoreOf hJT hTJ
  rw [twoResidual_eq_oTwoUpper'] at hii
  have hlt := hii.mpr hJO
  rw [← hKeq] at hlt
  exact lt_irrefl _ hlt

theorem e23_F4 (h331 : Stmt3_3_1_F4) (h5172 : Stmt5_1_7_two_F4) (he23 : E2.E23Statement) :
    E2.E23Concl H T (UH T H) c.UH_red.1 :=
  he23 G H T (H ⊓ M) (UH T H) c.UH_red.1 (c.minParabolic_F4 h331) c.sqtk c.charTwo c.UH_red.2
    (c.thompsonJ_not_le_F4 h331 h5172)

end Cx615

end CFSG.Quasithin.H13
