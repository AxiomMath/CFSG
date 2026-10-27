module

public import CFSG.GH74.Generic.S1.Exo.Q3H
public import CFSG.GH74.Generic.S1.Exo.Q3HII

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem rankTwoStmt_proved :
    RankTwoStmt :=
  fun G _ _ _ hnonab hrank => rank_two_isomorphism_types G hnonab hrank

theorem q3H_of_inputs (hR : RankTwoStmt) (hIV : ∀ (H : Type) [Group H] [Finite H] (c y : H) (JA JB :
    Subgroup H), Nbhd3Hyp H c y JA JB → ¬ ∃ N : Subgroup H, IsComponent N ∧ (∀ g ∈ JA, (∃ k : ℕ, g ^
    (2 ^ k) = 1) → g ∈ N) ∧ (∀ g ∈ JB, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ N)) : Q3H := by
  intro H _ _ c y JA JB h u hu P hPs hP360 hPl hPu hmax
  have hP1 : P ≠ ⊥ := by
    intro hP
    rw [hP, Subgroup.card_bot] at hP360
    omega
  obtain ⟨N, ψA, ψB, hr, hcase⟩ := h.reduce hPl hP1
  rcases hcase with hII | ⟨hA, hB⟩
  · exact q3_caseII hR h hr hII hu hPs hP360 hPl hPu hmax
  · exact hIV H c y JA JB h ⟨N, hr.comp, hA, hB⟩

end CFSG.GH74.Generic.S1.Exo
