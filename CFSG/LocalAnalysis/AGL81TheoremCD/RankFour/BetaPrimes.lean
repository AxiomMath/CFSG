module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC6

variable {G : Type} [Group G] [Finite G]

theorem le_of_mem_uniqueFourBeta (hU : CFSG.Open.uniqueFourUnique G) {M : Subgroup G}
    (hM : CFSG.Open.uniqueFourIsMaxTwoLocal M) {q : ℕ} (hq : q ∈ CFSG.Open.uniqueFourBeta G)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQ : IsPGroup q Q) (hQ2 : 2 ≤ CFSG.Open.pRank q Q)
    {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M := by
  haveI : Fact q.Prime := ⟨hq.1⟩
  obtain ⟨N, hN, hqN⟩ := exists_maxLocal_mem_sigma hq
  obtain ⟨S, hSN, -⟩ := exists_sylow_le_of_sigma hU hN hqN
  obtain ⟨g, hg⟩ := exists_le_uniqueFourConj_sylow hQ S
  have hN' : CFSG.Open.uniqueFourIsMaxTwoLocal (uniqueFourConj g N) := isMaxTwoLocal_conj hN g
  have hqN' : q ∈ CFSG.Open.uniqueFourSigma (uniqueFourConj g N) :=
    mem_uniqueFourSigma_conj hqN g
  have hQN' : Q ≤ uniqueFourConj g N := hg.trans (uniqueFourConj_mono hSN g)
  have hMN' : M ≤ uniqueFourConj g N := sec61 hU hN' hqN' hQN' hQ2 hM.1 hQM
  have heq : uniqueFourConj g N = M := hM.2 _ hN'.1 hMN'
  have hqM : q ∈ CFSG.Open.uniqueFourSigma M := by
    rw [← heq]
    exact hqN'
  exact sec61 hU hM hqM hQM hQ2 hH hQH

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
