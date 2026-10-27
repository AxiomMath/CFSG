module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3K1L34
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3K1Out
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3K1Spor

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Certificates

theorem kFactSmallAutRank_of_noBM (h1 : StronglyEmbeddedRankTwoKFactNoBM)
    (hOutSpor : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)) :
    KFactSmallAutRank := by
  intro K _ _ hs hnab hcat p hp hp2 T hnc hGLB hrk
  have hZ := center_eq_bot_of_isSimpleGroup_of_nonabelian hs hnab
  have hrk2 : Open.pRank p (T : Subgroup K) = 2 :=
    le_antisymm hrk (two_le_pRank_of_not_isCyclic hp hp2 T.isPGroup' hnc)
  have hOut : ¬ p ∣ Nat.card (Outer K) → Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 :=
    fun hnd => (pRank_mulAut_le_of_not_dvd_card_outer hp hZ T hnd).trans hrk
  by_cases hBM : NotBM K
  · have hSE := h1 K hs hnab hcat hBM p hp hp2 T hrk2 hGLB
    have hnd2 : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
    rcases hSE with ⟨hf, ⟨f⟩⟩ | ⟨q, hq1, hq2, hl⟩ | ⟨h5, ⟨f⟩⟩ | ⟨h3, h⟩ | ⟨h5, h⟩ | ⟨h11, ⟨f⟩⟩
    · exact pRank_mulAut_le_two_of_psl2 hp2 f
    · have : Fact p.Prime := ⟨hp⟩
      exact pRank_mulAut_le_two_of_unitary q hq1 hq2 hl
    · exact hOut (not_dvd_card_outer_of_alternating (by omega) f hp hp2)
    · subst h3
      rcases h with ⟨q, hq1, hq2, ⟨hv, ⟨e⟩⟩⟩ | hf
      · exact pRank_mulAut_le_two_of_isLinThreeFour ⟨⟨.A 2 q, hv⟩, ⟨q, hq1, hq2, rfl⟩, ⟨e⟩⟩
      · obtain ⟨f⟩ := hf
        exact hOut (not_dvd_card_outer_M11 f hp hp2)
    · subst h5
      rcases h with hl | hf | hf
      · exact hOut (by rw [card_outer_of_tits hl]; exact hnd2)
      · obtain ⟨f⟩ := hf
        exact hOut (not_dvd_card_outer_McL f hp hp2)
      · obtain ⟨f⟩ := hf
        exact hOut (not_dvd_card_outer_Fi22 f hp hp2)
    · subst h11
      exact hOut (not_dvd_card_outer_J4 f hp hp2)
  · have hex : ∃ s : TauCeti.SporadicName,
        Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) := by
      unfold NotBM at hBM
      rw [not_and_or, not_not, not_not] at hBM
      rcases hBM with h | h
      · exact ⟨.B, h⟩
      · exact ⟨.M, h⟩
    obtain ⟨s, ⟨e⟩⟩ := hex
    refine hOut ?_
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact hOutSpor s p hp hp2

theorem kFactBetaRank2_of_noBM (hOut : KFactOutCyclic) (h1 : StronglyEmbeddedRankTwoKFactNoBM)
    (hOutSpor : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)) :
    KFactBetaRank2 :=
  kFactBetaRank2_of hOut (kFactSmallAutRank_of_noBM h1 hOutSpor)

end Certificates

end CFSG.LocalAnalysis.RankThreeTheoremC
