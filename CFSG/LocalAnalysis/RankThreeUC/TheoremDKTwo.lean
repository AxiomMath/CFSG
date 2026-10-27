module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
import CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_two_pow_mem_of_odd_orderOf {H : Subgroup G} {x : G} (hx : Odd (orderOf x))
    {k : ℕ} (h : x ^ 2 ^ k ∈ H) : x ∈ H := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx))
  exact hm ▸ H.pow_mem h m

end CFSG.LocalAnalysis.RankThreeUC
