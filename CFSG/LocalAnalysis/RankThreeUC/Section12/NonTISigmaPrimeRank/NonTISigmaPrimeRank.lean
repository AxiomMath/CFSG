module

public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISigmaPrimeRank

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem sigma_prime_rank {M : Subgroup G} {p : ℕ} (hp : p ∈ SourceSetting.sigmaOf G M) :
    p.Prime ∧ p ≠ 2 ∧ 3 ≤ CFSG.Assembly.pRank p M := by
  have prime_ne_two_rank_of_mem_sigmaA {p : ℕ} (h : p ∈ rankThreeSigmaA G) :
      p.Prime ∧ p ≠ 2 ∧ 3 ≤ rankThreeLocalRank p G := by
    unfold rankThreeSigmaA at h
    dsimp only at h
    split_ifs at h with h1 h2 h3
    · exact ⟨h.1, h.2.1, by have := h.2.2.2; omega⟩
    · exact ⟨h.1, by have := h.2.1; omega, by have := h.2.2.2; omega⟩
    · exact ⟨h.1, by have := h.2.1; omega, by have := h.2.2.2; omega⟩
    · exact ⟨h.1, h.2.1, by have := h.2.2.2; omega⟩
  obtain ⟨hσ, P0, hw⟩ := (SourceSetting.sigmaOf_mem_iff M p).mp hp
  obtain ⟨hpp, hp2, hr⟩ := prime_ne_two_rank_of_mem_sigmaA hσ
  have : Fact p.Prime := ⟨hpp⟩
  refine ⟨hpp, hp2, ?_⟩
  obtain ⟨H, -, hHr⟩ := CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_attained p
    (G := G) (by omega)
  have h3 : 3 ≤ CFSG.Open.pRank p (P0 : Subgroup G) := by
    rw [(CFSG.SectionRank.pRank_sylow P0).1]
    calc 3 ≤ CFSG.Open.pRank p H := by omega
      _ ≤ _ := CFSG.SectionRank.pRank_mono hpp.one_lt le_top
  have hPM : (P0 : Subgroup G) ≤ M := by
    refine Subgroup.le_normalizer.trans (hw.u0.trans' ?_)
    exact le_sSup ⟨(P0 : Subgroup G), le_rfl, by omega, rfl⟩
  exact h3.trans (CFSG.SectionRank.pRank_mono hpp.one_lt hPM)

end CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISigmaPrimeRank
