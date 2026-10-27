module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.IsElemAbelianOfBinaryRankCounterexample
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryRankGreaterThanThree
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryPrimeExclusionFromRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem three_lt_pRank_and_prime_not_dvd_card_actor {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    3 < CFSG.Open.pRank p P ∧ p ∉ piOf B := by
  have hEA := isElemAbelian_of_binary_rank_counterexample hc
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  have hRank := ElementaryRankGreaterThanThree.three_lt_pRank hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction hEA
  exact ⟨hRank, ElementaryPrimeExclusionFromRank.p_not_mem_piOf hc hEA hRank⟩

end Section5
end CFSG.LocalAnalysis.RankThreeUC
