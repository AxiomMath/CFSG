module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem517S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V W H : Subgroup G} {n : ℕ}

namespace Hyp5_0_1

variable (h : Hyp5_0_1 G T M L n)
include h

theorem dichotomy_F4 (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h512 : Stmt5_1_2_F4) (hW : IsCh5Module T L W) (hH : IsHStar T M H) :
    (⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧ W ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∨
      (⁅W, thompsonJ T⁆ ≠ ⊥ ∧ (IsNatQuotCh5 L W n ∨
        (n = 2 ∧ IsCommCentralSplit L T W ∧ IsBarS5 L T W ∧ IsS5ModCh5 L T ⁅W, L⁆))) := by
  rcases theorem318_three hC58 h317 h.simple h.nonabelian h.qtke h.sylow
      (h.hyp318_F4 h331 hW hH) with ⟨hJ, -⟩ | ⟨-, hZ, hZ0⟩
  · right
    rcases h512 G T M L W n h hW with ⟨h1, -⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact absurd (le_inf (thompsonJ_le_self T) (h1.trans inf_le_right)) hJ
    · exact ⟨h2, Or.inl h3⟩
    · exact ⟨h2, Or.inr h3⟩
  · left
    refine ⟨?_, h.module_inf_centralizer_eq_bot hW hZ0⟩
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ((hZ H hH).trans inf_le_right)

end Hyp5_0_1

end CFSG.Quasithin.H13
