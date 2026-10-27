module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Linear
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.SectionRank.ClassicalEven

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem sqt_even_classical_restriction {S : Type} [Group S] [Finite S]
    (hSQT : ∀ q : ℕ, q.Prime → q ≠ 2 → pRank q (⊤ : Subgroup S) ≤ 2)
    {t : StatedLieTag} {n f : ℕ} (h : StatedClassicalModel S t n 2 f) :
    (t = .PSL ∧ n = 2 ∧ 2 ≤ f) ∨ (t = .PSL ∧ n = 3 ∧ 1 ≤ f) ∨
      (t = .PSL ∧ (n = 4 ∨ n = 5) ∧ f = 1) ∨ (t = .PSU ∧ n = 3 ∧ 2 ≤ f) ∨
      (t = .PSp ∧ n = 2 ∧ 2 ≤ f) := by
  obtain ⟨⟨-, hf, hadm⟩, hmod⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Nat.Prime 3 := Nat.prime_three
  cases t with
  | PSL =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    obtain ⟨hn2, h22, -⟩ := hadm
    have : CharP K 2 := ClassicalOdd.charP_of_card hK
    have htorus : ∀ m, 4 ≤ m → n = m → f = 1 := fun m hm hnm => by
      by_contra hne
      subst hnm
      obtain ⟨r, hr, hr2, hrank⟩ := psl_torus_three_le_pRank hK (by omega) hm
      exact false_of_three_le_pRank hSQT e hr hr2 hrank
    rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with
      rfl | rfl | rfl | rfl | hn6
    · refine Or.inl ⟨rfl, rfl, ?_⟩
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact h22 (by norm_num)
    · exact Or.inr (Or.inl ⟨rfl, rfl, hf⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl, htorus 4 le_rfl rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl, htorus 5 (by norm_num) rfl⟩))
    · exact (false_of_three_le_pRank hSQT e h3 (by norm_num)
        (psl_three_le_pRank_three hn6)).elim
  | PSU =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    obtain ⟨hn3, h32⟩ := hadm
    rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_⟩)))
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact h32 (by norm_num)
    · obtain ⟨r, hr, hr2, hrank⟩ := psu_torus_three_le_pRank hK hf hn4
      exact (false_of_three_le_pRank hSQT e hr hr2 hrank).elim
  | PSp =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    obtain ⟨hn2, h22⟩ := hadm
    have : CharP K 2 := ClassicalOdd.charP_of_card hK
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)))
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact h22 (by norm_num)
    · exact (false_of_three_le_pRank hSQT e h3 (by norm_num)
        (psp_three_le_pRank_three hn3)).elim
  | POmegaOdd => exact (hadm.2 rfl).elim
  | POmegaPlus =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    have : CharP K 2 := ClassicalOdd.charP_of_card hK
    exact (false_of_three_le_pRank hSQT e h3 (by norm_num)
      (omegaPlus_three_le_pRank_three hadm)).elim
  | POmegaMinus =>
    obtain ⟨K, _, _, hK, b, c, -, ⟨e⟩⟩ := hmod
    have : CharP K 2 := ClassicalOdd.charP_of_card hK
    exact (false_of_three_le_pRank hSQT e h3 (by norm_num)
      (omegaMinus_three_le_pRank_three hadm b c)).elim
  | _ => exact hmod.elim

end CFSG.SectionRank.ClassicalEven
