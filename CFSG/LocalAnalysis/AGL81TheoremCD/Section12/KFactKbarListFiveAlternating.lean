module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Census
import CFSG.LieType.Simplicity.Basic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

open CFSG.Open Subgroup

theorem degree_lt_twelve_of_alternating {K S : Type} [Group K] [Finite K]
    [Group S] [Finite S] (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S)
    {n : ℕ} (hn : 5 ≤ n) (a : K ≃* alternatingGroup (Fin n))
    {Y : Subgroup (MulAut S)} (hY : (MulAut.conj : S →* MulAut S).range ≤ Y)
    (hr : CFSG.Open.pRank 3 Y ≤ 3) : n < 12 := by
  have : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_alternating_converse K
    ⟨n, hn, ⟨a⟩⟩).2.2
  have hK := (pRank_top_le_of_centerQuotient hq e (by norm_num) hY).trans hr
  by_contra h
  have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.a6c_four_le_pRank_alt (by omega : 12 ≤ n)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) a] at h4
  omega

theorem alternating_two_mul {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    {p : ℕ} (hp : 5 ≤ p) (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S)
    (a : K ≃* alternatingGroup (Fin (2 * p)))
    {Y : Subgroup (MulAut S)} (hY : (MulAut.conj : S →* MulAut S).range ≤ Y)
    (hr : CFSG.Open.pRank 3 Y ≤ 3) :
    p = 5 ∧ Nonempty (S ≃* alternatingGroup (Fin 10)) := by
  have hn := degree_lt_twelve_of_alternating hq e (by omega) a hY hr
  have hp5 : p = 5 := by omega
  subst p
  have : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_alternating_converse K
    ⟨10, by norm_num, ⟨a⟩⟩).2.2
  exact ⟨rfl, ⟨(equiv_of_centerQuotient hq e).symm.trans a⟩⟩

theorem false_of_alternating_three_mul {K S : Type} [Group K] [Finite K]
    [Group S] [Finite S] {p : ℕ} (hp : 5 ≤ p) (hq : CFSG.IsQuasisimple K)
    (e : K ⧸ center K ≃* S) (a : K ≃* alternatingGroup (Fin (3 * p)))
    {Y : Subgroup (MulAut S)} (hY : (MulAut.conj : S →* MulAut S).range ≤ Y)
    (hr : CFSG.Open.pRank 3 Y ≤ 3) : False := by
  have := degree_lt_twelve_of_alternating hq e (by omega) a hY hr
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

end
