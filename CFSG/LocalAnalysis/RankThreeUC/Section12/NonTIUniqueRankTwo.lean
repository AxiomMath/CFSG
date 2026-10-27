module


public import CFSG.LocalAnalysis.RankThreeUC.Section12.Context
public import CFSG.LocalAnalysis.RankThreeUC.WitnessNoncyclicUniqueness

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section12.NonTIUniqueRankTwo

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem unique_of_rank_two {M T X : Subgroup G} (hc : Context G M T) {p : ℕ}
    (hp : p ∈ SourceSetting.sigmaOf G M) (hXM : X ≤ M) (hX : 2 ≤ CFSG.Assembly.pRank p X)
    (N : Subgroup G) (hN : rankThreeIsMaxTwoLocal N) (hXN : X ≤ N) : N = M := by
  obtain ⟨q, P, -, -, hw⟩ := SourceSetting.IsInMSigma.exists hc.mSigma
  have hMmax : rankThreeIsMaxTwoLocal M := hw.maxLocal
  have hpp : p.Prime := (NonTISigmaPrimeRank.sigma_prime_rank hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨E, hEX, hE, hcard⟩ := SectionRank.exists_pRank hpp.one_lt X
  have hpE : IsPGroup p E := by
    rw [IsPGroup.iff_card]
    exact ⟨_, hcard⟩
  have hnc : ¬ IsCyclic E := by
    intro hcyc
    have hexp : Monoid.exponent E ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro g
      exact Subtype.ext (by simpa using hE.2 (g : G) g.2)
    have h1 : Nat.card E ≤ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact Nat.le_of_dvd hpp.pos hexp
    have h2 : p ^ 2 ≤ p ^ CFSG.Open.pRank p X := Nat.pow_le_pow_right hpp.pos hX
    rw [hcard] at h1
    have h3 : 2 ≤ p := hpp.two_le
    nlinarith
  have hmax : SourceSetting.maxTwoLocalsContaining E = {M} :=
    WitnessNoncyclicUniqueness.maxTwoLocalsContaining_eq_singleton hp hMmax (hEX.trans hXM) hpE hnc
  have hNmem : N ∈ SourceSetting.maxTwoLocalsContaining E := ⟨hN, hEX.trans hXN⟩
  rw [hmax] at hNmem
  exact hNmem

end CFSG.LocalAnalysis.RankThreeUC.Section12.NonTIUniqueRankTwo
