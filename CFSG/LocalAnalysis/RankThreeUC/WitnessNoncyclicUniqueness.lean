module



public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
public import CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISigmaPrimeRank.NonTISigmaPrimeRank

public section


namespace CFSG.LocalAnalysis.RankThreeUC.WitnessNoncyclicUniqueness


open CFSG.Open


variable {G : Type} [Group G] [Finite G]


theorem two_le_pRank_of_noncyclic {M X : Subgroup G} {p : ℕ}
    (hp : p ∈ CFSG.LocalAnalysis.RankThreeUC.SourceSetting.sigmaOf G M) (hXp : IsPGroup p X) (hX : ¬ IsCyclic X) :
    2 ≤ CFSG.Open.pRank p X := by
  obtain ⟨hpp, hp2, -⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISigmaPrimeRank.sigma_prime_rank hp
  by_contra h
  exact hX (CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one hpp hp2 hXp
    (by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; omega))


theorem le_of_isTwoLocal_of_noncyclic {M X : Subgroup G} {p : ℕ}
    (hp : p ∈ CFSG.LocalAnalysis.RankThreeUC.SourceSetting.sigmaOf G M) (hXM : X ≤ M) (hXp : IsPGroup p X)
    (hX : ¬ IsCyclic X) {H : Subgroup G} (hH : IsTwoLocal H) (hXH : X ≤ H) : H ≤ M := by
  obtain ⟨-, P, hw⟩ := (CFSG.LocalAnalysis.RankThreeUC.SourceSetting.sigmaOf_mem_iff M p).mp hp
  have hpp := (CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISigmaPrimeRank.sigma_prime_rank hp).1
  have h2 := two_le_pRank_of_noncyclic hp hXp hX
  refine hw.u2 H hH (h2.trans ?_)
  exact CFSG.SectionRank.pRank_mono hpp.one_lt (le_inf hXH hXM)


theorem maxTwoLocalsContaining_eq_singleton {M X : Subgroup G} {p : ℕ}
    (hp : p ∈ CFSG.LocalAnalysis.RankThreeUC.SourceSetting.sigmaOf G M) (hM : rankThreeIsMaxTwoLocal M)
    (hXM : X ≤ M) (hXp : IsPGroup p X) (hX : ¬ IsCyclic X) :
    CFSG.LocalAnalysis.RankThreeUC.SourceSetting.maxTwoLocalsContaining X = {M} := by
  ext N
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hN
    have hNM := le_of_isTwoLocal_of_noncyclic hp hXM hXp hX hN.1.1 hN.2
    exact (hN.1.2 M hM.1 hNM).symm
  · rintro rfl
    exact ⟨hM, hXM⟩


end CFSG.LocalAnalysis.RankThreeUC.WitnessNoncyclicUniqueness
