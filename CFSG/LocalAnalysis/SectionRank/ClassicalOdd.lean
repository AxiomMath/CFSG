module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Symplectic
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Unitary
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Orthogonal
public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Assembly.LowTwoRank ClassicalOdd

theorem classical_model_rank {G : Type} [Group G] [Finite G] {t : StatedLieTag} {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel G t n p f) :
    p.Prime ∧ 1 ≤ f ∧
      ((t = .PSL ∧ ((n = 2 ∧ f ≤ pRank p (⊤ : Subgroup G)) ∨
          (n = 3 ∧ 2 * f ≤ pRank p (⊤ : Subgroup G)) ∨ 4 ≤ pRank p (⊤ : Subgroup G))) ∨
        (t = .PSU ∧ ((n = 3 ∧ 2 * f ≤ pRank p (⊤ : Subgroup G)) ∨
          4 ≤ pRank p (⊤ : Subgroup G))) ∨
        (t = .PSp ∧ ((n = 2 ∧ 3 * f ≤ pRank p (⊤ : Subgroup G)) ∨
          4 ≤ pRank p (⊤ : Subgroup G))) ∨
        4 ≤ pRank p (⊤ : Subgroup G)) := by
  obtain ⟨⟨hp, hf, hadm⟩, hmod⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  refine ⟨hp, hf, ?_⟩
  cases t with
  | PSL =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    obtain ⟨hn2, -, -⟩ := hadm
    rw [pRank_top_eq_of_mulEquiv hp1 e]
    refine Or.inl ⟨rfl, ?_⟩
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | hn4
    · exact Or.inl ⟨rfl, by simpa using le_pRank_SL (a := 1) (b := 1) le_rfl le_rfl hK⟩
    · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      simpa [mul_comm] using le_pRank_SL (a := 1) (b := 2) le_rfl le_rfl hK
    · have := le_pRank_SL (a := 2) (b := 2) (by norm_num) hn4 hK
      exact Or.inr (Or.inr (by omega))
  | PSU =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    obtain ⟨hn3, -⟩ := hadm
    rw [pRank_top_eq_of_mulEquiv hp1 e]
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
    · exact Or.inl ⟨rfl, two_mul_le_pRank_SU_three hp2 hK⟩
    · have := four_mul_le_pRank_SU hp2 hn4 hK
      exact Or.inr (by omega)
  | PSp =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    obtain ⟨hn2, -⟩ := hadm
    rw [pRank_top_eq_of_mulEquiv hp1 e]
    refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
    have := le_pRank_Sp hn2 hK
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact Or.inl ⟨rfl, by omega⟩
    · refine Or.inr (le_trans ?_ this)
      nlinarith
  | POmegaOdd =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    obtain ⟨hn3, -⟩ := hadm
    rw [pRank_top_eq_of_mulEquiv hp1 e]
    have := four_mul_le_pRank_omegaOdd hn3 hp2 hK
    exact Or.inr (Or.inr (Or.inr (by omega)))
  | POmegaPlus =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod
    rw [pRank_top_eq_of_mulEquiv hp1 e]
    have := four_mul_le_pRank_omegaPlus hadm hp2 hK
    exact Or.inr (Or.inr (Or.inr (by omega)))
  | POmegaMinus =>
    obtain ⟨K, _, _, hK, b, c, -, ⟨e⟩⟩ := hmod
    rw [pRank_top_eq_of_mulEquiv hp1 e]
    have := four_mul_le_pRank_omegaMinus hadm b c hp2 hK
    exact Or.inr (Or.inr (Or.inr (by omega)))
  | _ => exact hmod.elim

theorem classical_odd_central_quotient_bound {G : Type} [Group G] [Finite G]
    (hG : ∀ q : ℕ, q.Prime → q ≠ 2 → pRank q (⊤ : Subgroup G) ≤ 2)
    (A : Subgroup G) [A.Normal] (hAZ : A ≤ Subgroup.center G)
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (h : StatedClassicalModel (G ⧸ A) t n p f) :
    (t = .PSL ∧ ((n = 2 ∧ f ≤ 3) ∨ (n = 3 ∧ f = 1))) ∨ (t = .PSU ∧ n = 3 ∧ f ≤ 3) ∨
      (t = .PSp ∧ n = 2 ∧ f = 1) := by
  obtain ⟨hp, hf, hr⟩ := classical_model_rank hp2 h
  have : Fact p.Prime := ⟨hp⟩
  have h3 := pRank_quotient_le_three hp2 (hG p hp hp2) A hAZ
  rcases hr with ⟨ht, (⟨hn, hr⟩ | ⟨hn, hr⟩ | hr)⟩ | ⟨ht, (⟨hn, hr⟩ | hr)⟩ |
      ⟨ht, (⟨hn, hr⟩ | hr)⟩ | hr
  · exact Or.inl ⟨ht, Or.inl ⟨hn, by omega⟩⟩
  · exact Or.inl ⟨ht, Or.inr ⟨hn, by omega⟩⟩
  · omega
  · exact Or.inr (Or.inl ⟨ht, hn, by omega⟩)
  · omega
  · exact Or.inr (Or.inr ⟨ht, hn, by omega⟩)
  · omega
  · omega

theorem sqt_odd_classical_restriction {X : Type} [Group X] [Finite X]
    (hX : ∀ q : ℕ, q.Prime → q ≠ 2 → pRank q (⊤ : Subgroup X) ≤ 2)
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (h : StatedClassicalModel X t n p f) :
    (t = .PSL ∧ n = 2 ∧ (f = 1 ∨ f = 2)) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨
      (t = .PSU ∧ n = 3 ∧ f = 1) := by
  obtain ⟨hp, hf, hr⟩ := classical_model_rank hp2 h
  have h2 := hX p hp hp2
  rcases hr with ⟨ht, (⟨hn, hr⟩ | ⟨hn, hr⟩ | hr)⟩ | ⟨ht, (⟨hn, hr⟩ | hr)⟩ |
      ⟨ht, (⟨hn, hr⟩ | hr)⟩ | hr
  · exact Or.inl ⟨ht, hn, by omega⟩
  · exact Or.inr (Or.inl ⟨ht, hn, by omega⟩)
  · omega
  · exact Or.inr (Or.inr ⟨ht, hn, by omega⟩)
  · omega
  · omega
  · omega
  · omega

end CFSG.SectionRank
