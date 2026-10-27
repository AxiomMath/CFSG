module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6StatementsS331
public import CFSG.Quasithin.Vol2.Ch6Remark612

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem stmt6_1_2_F4 (h512 : Stmt5_1_2_F4) (h513 : Stmt5_1_3_F4) : Stmt6_1_2_F4 := by
  intro G _ _ T M L V n h
  have hL : ⁅L, L⁆ = L := h.toHyp5_0_1.commutator_eq
  have hT : IsPGroup 2 T := h.sylow.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  refine ⟨?_, ?_⟩
  · rcases h513 G T M L V n h.toHyp5_0_1 h.module with
      h1 | ⟨h2n, -, h2⟩ | h3 | h4 | ⟨-, h5S, h5⟩
    · exact Or.inl h1
    · exact absurd ⟨h2n, (isA5ModuleSum_of_s5 (Or.inr h2) hL hT hTL).commutator⟩ h.not_a5
    · exact Or.inr (Or.inl h3)
    · by_cases hn : n = 2
      · exact absurd ⟨hn, (hn ▸ h4 : IsOrthCh5 L V 2).isA5ModuleSum_commutator⟩ h.not_a5
      · exact Or.inr (Or.inr ⟨by have := h.two_le; omega, h4⟩)
    · exact absurd ⟨h.toHyp5_0_1.n_eq_two_of_isBarS5_r612 h.module h5S,
        isA5ModuleSum_of_s5 (Or.inl h5) hL hT hTL⟩ h.not_a5
  · rcases h512 G T M L V n h.toHyp5_0_1 h.module with
      ⟨hJ, hJN, -, hJU, -⟩ | ⟨-, h2⟩ | ⟨-, h3n, -, -, h3⟩
    · exact Or.inr ⟨le_inf (GammaExtra.thompsonJ_le fun A hA => hA.1) (hJ.trans inf_le_right),
        h.centralizer_eq, hJN, hJU⟩
    · exact Or.inl h2.commutator
    · exact absurd ⟨h3n, isA5ModuleSum_of_s5 (Or.inl h3) hL hT hTL⟩ h.not_a5

end CFSG.Quasithin.H13
