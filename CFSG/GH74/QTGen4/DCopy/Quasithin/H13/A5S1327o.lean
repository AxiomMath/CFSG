module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.H13.A5S1327b
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem thompsonJ_not_le_centralizer_UH_F4 (h331 : Stmt3_3_1_F4)
    (h5172 : Stmt5_1_7_two_F4) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (S.UH H : Set G) := by
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hZH' : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  obtain ⟨-, hLHJ, -⟩ := h5172 G T _ L V H 2 h501 S.isCh5Module hH hZH'
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar_F4 h331 hH
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨-, -, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hZU : quasithinOmegaOneCenter T ≤ S.UH H := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  intro hJ
  have h1 := (hMP.le_pCoreOf_iff_le_centralizer hUred hHU (thompsonJ T)).mpr
    (le_inf (thompsonJ_le_self T) hJ)
  have h2 := (hMP.commutator_lt_iff_le_pCoreOf (thompsonJ_le_self T)
    (B2F.R_le_normalizer_thompsonJ T)).mpr h1
  rw [twoResidual_eq_oTwoUpper', ← hLHJ] at h2
  exact lt_irrefl _ h2

end Setting

end CFSG.Quasithin.H13.A5
