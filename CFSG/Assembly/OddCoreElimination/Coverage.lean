module

public import CFSG.Assembly.OddCoreEliminationStatements
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage

public section

namespace CFSG.Assembly.Dichotomy

theorem derivedInvolutionCoverage {G : Type*} [Group G] [Finite G] (hrank : 3 ≤ twoRank G)
    {t : G} (htG : t ∈ commutator G) (ht : orderOf t = 2) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E :=
  CFSG.ProperTwoGeneratedCore.derived_involution_rank_three_coverage hrank t ht htG

theorem perfectInvolutionCoverage : PerfectInvolutionCoverageStatement := by
  intro G _ _ hperf hrank t ht
  exact derivedInvolutionCoverage hrank (hperf ▸ Subgroup.mem_top t) ht

end CFSG.Assembly.Dichotomy
