module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.QuasithinUnique.Vol2Native.EvenWit

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.ClassicalEven
  CFSG.QuasithinUnique.Setup.Family

theorem oddRankOneEvenClassical : OddRankOneEvenClassicalProp := by
  intro S _ _ hS t n f hm
  have hex : ∀ {r : ℕ}, r.Prime → r ≠ 2 → 2 ≤ CFSG.pRank r S → False := fun hr hr2 h => by
    have := hS _ hr hr2
    omega
  have hex' : (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S) → False :=
    fun ⟨_, hr, hr2, h⟩ => hex hr hr2 h
  have h3 : Nat.Prime 3 := Nat.prime_three
  cases t with
  | PSL =>
    obtain ⟨-, hf, hn2, h22, -⟩ := hm.1
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | hn4
    · refine Or.inl ⟨rfl, rfl, ?_⟩
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact h22 (by norm_num)
    · by_cases hf1 : f = 1
      · exact Or.inr ⟨rfl, rfl, hf1⟩
      · exact (hex' (exists_two_le_pRank_psl_three_even (by omega) hm)).elim
    · exact (hex' (exists_two_le_pRank_psl_of_four_le hn4 hm)).elim
  | PSU =>
    obtain ⟨-, hf, hn3, h32⟩ := hm.1
    rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
    · have hf2 : 2 ≤ f := by
        by_contra hlt
        obtain rfl : f = 1 := by omega
        exact h32 (by norm_num)
      exact (hex' (exists_two_le_pRank_psu_three_even hf2 hm)).elim
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      obtain ⟨r, hr, hr2, hrank⟩ := psu_torus_three_le_pRank hK hf hn4
      exact (hex hr hr2 (two_le_pRank_of_mulEquiv hr e (le_trans (by norm_num) hrank))).elim
  | PSp =>
    obtain ⟨-, -, hn2, -⟩ := hm.1
    exact (hex' (exists_two_le_pRank_psp_of_two_le hn2 hm)).elim
  | POmegaOdd =>
    obtain ⟨-, -, hadm⟩ := hm.1
    exact (hadm.2 rfl).elim
  | POmegaPlus =>
    obtain ⟨⟨-, -, hadm⟩, hmod⟩ := hm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    have : CharP K 2 := ClassicalOdd.charP_of_card hK
    exact (hex h3 (by norm_num) (two_le_pRank_of_mulEquiv h3 e
      (le_trans (by norm_num) (omegaPlus_three_le_pRank_three hadm)))).elim
  | POmegaMinus =>
    obtain ⟨⟨-, -, hadm⟩, hmod⟩ := hm
    obtain ⟨K, _, _, hK, b, c, -, ⟨e⟩⟩ := hmod
    have : CharP K 2 := ClassicalOdd.charP_of_card hK
    exact (hex h3 (by norm_num) (two_le_pRank_of_mulEquiv h3 e
      (le_trans (by norm_num) (omegaMinus_three_le_pRank_three hadm b c)))).elim
  | _ => exact False.elim hm.2

end CFSG.QuasithinUnique.Vol2Native.EvenWit
