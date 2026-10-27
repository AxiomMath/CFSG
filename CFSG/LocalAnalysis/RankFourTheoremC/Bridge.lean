module

public import CFSG.LocalAnalysis.RankFourTheoremC.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem weakCore_le_of_large_subgroup (hpre : GLBPreuniqueness G) (hD1 : D1For G) {p : ℕ}
    (hp : p ∈ GLBBetaFour G) (P : Sylow p G) (hP : 3 ≤ pRank p (P : Subgroup G))
    {M E : Subgroup G} (hM : GLBIsMaxTwoLocal M) (hEP : E ≤ P) (hEM : E ≤ M)
    (hE : 3 ≤ pRank p E) : GLBWeakCore p (P : Subgroup G) ≤ M := by
  obtain ⟨Y, hY, hWY⟩ := (hpre p hp).2 P
  obtain ⟨L, hYL, hL⟩ := exists_maximal_twoLocal hY
  have hWL : GLBWeakCore p (P : Subgroup G) ≤ L := hWY.trans hYL
  have hPL : (P : Subgroup G) ≤ L := (subgroup_le_weakCore_of_rank p hp.1 _ hP).trans hWL
  have hML : M ≤ L :=
    hD1 p hp P L hL hWL M hM.1 (hE.trans (pRank_mono p hp.1 (le_inf hEM (hEP.trans hPL))))
  rw [← hM.2 L hL.1 hML]
  exact hWL

theorem exists_core_of_mem_sigma (hpre : GLBPreuniqueness G) (hD1 : D1For G) {M : Subgroup G}
    (hM : GLBIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ GLBSigma M) :
    ∃ P : Sylow p G, D1Local p P M := by
  obtain ⟨hpβ, B, hB, hBM⟩ := hp
  obtain ⟨P, hBP, hP4⟩ := bmax_has_large_sylow hpβ hB
  have hB4 : 4 ≤ pRank p B := hpβ.2.2.2.trans (bmax_rank_lowerBound hpβ.1 hB)
  exact ⟨P, ⟨hpβ, hM, weakCore_le_of_large_subgroup hpre hD1 hpβ P (by omega) hM hBP hBM
    (by omega)⟩⟩

theorem almostStrongMaximalLocals_of_atCore (hpre : GLBPreuniqueness G) (hD1 : D1For G)
    (hE1 : AlmostStrongAtCore G) : AlmostStrongMaximalLocals G := by
  intro M hM p hp
  obtain ⟨P, hloc⟩ := exists_core_of_mem_sigma hpre hD1 hM hp
  exact hE1 p P M hloc

theorem rankTwoConfinement_of_atCore (hpre : GLBPreuniqueness G) (hD1 : D1For G)
    (hE2 : ConfinementAtCore G) : RankTwoConfinement G := by
  intro M hM p hp H hH h2
  obtain ⟨P, hloc⟩ := exists_core_of_mem_sigma hpre hD1 hM hp
  exact hE2 p P M hloc H hH h2

theorem glbUniqueFour_iff :
    GLBUniqueFour G ↔ AlmostStrongMaximalLocals G ∧ RankTwoConfinement G := by
  constructor
  · intro h
    refine ⟨fun M hM p hp => ?_, fun M hM p hp H hH h2 => ?_⟩
    · exact (h M hM ⟨p, hp⟩).1 p hp
    · exact (h M hM ⟨p, hp⟩).2 H hH ⟨p, hp, h2⟩
  · rintro ⟨h1, h2⟩ M hM _
    exact ⟨fun p hp => h1 M hM p hp, fun H hH ⟨p, hp, hr⟩ => h2 M hM p hp H hH hr⟩

end CFSG.LocalAnalysis.RankFourTheoremC
