module

public import CFSG.LocalAnalysis.RankFourTheoremC.Refined
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem four_le_pRank_sylow {p : ℕ} (hp : p ∈ GLBBetaFour G) (P : Sylow p G) :
    4 ≤ Open.pRank p (P : Subgroup G) := by
  have : Fact p.Prime := ⟨hp.1⟩
  rw [(CFSG.SectionRank.pRank_sylow P).1]
  exact betaFour_globalRank hp

theorem sylow_le_of_core {p : ℕ} {P : Sylow p G} {M : Subgroup G} (h : D1Local p P M) :
    (P : Subgroup G) ≤ M :=
  (subgroup_le_weakCore_of_rank p h.beta.1 _
    (by have := four_le_pRank_sylow h.beta P; omega)).trans h.core

theorem mem_sigma_of_core {p : ℕ} {P : Sylow p G} {M : Subgroup G} (h : D1Local p P M) :
    p ∈ GLBSigma M := by
  have hp := h.beta
  have : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨E, hEP, hE, hEcard⟩ := pRank_attained p hp.1 (P : Subgroup G)
  have hm : GLBTwoLocalRank p G ≤ Open.pRank p (P : Subgroup G) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact twoLocalRank_le_globalRank p hp.1
  have hdvd : p ^ GLBTwoLocalRank p G ∣ Nat.card E := hEcard ▸ pow_dvd_pow p hm
  obtain ⟨B, hBcard, -, hBE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp.1 (H := ⊥) (L := E) (by simp) hdvd bot_le
  have hBM : B ≤ M := (hBE.trans hEP).trans (sylow_le_of_core h)
  obtain ⟨U, hU, hU2, hMU⟩ := h.maxLocal.1
  refine ⟨hp, B, ⟨isElemAbelian_mono hE hBE, hBcard, U, hU, hU2, ?_⟩, hBM⟩
  rw [← hMU]
  exact hBM

theorem confinementAtCore_of_rankTwoConfinement (h : RankTwoConfinement G) :
    ConfinementAtCore G :=
  fun p _ M hloc H hH h2 => h M hloc.maxLocal p (mem_sigma_of_core hloc) H hH h2

end CFSG.LocalAnalysis.RankFourTheoremC
