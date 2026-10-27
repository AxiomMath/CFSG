module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralizerSylow
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.ComponentInitial

theorem involution_centralizer_contains_four_group {K : Type*} [Group K] [Finite K]
    (hK : 2 ≤ CFSG.pRank 2 K) {h : K} (hh : h ^ 2 = 1) :
    2 ≤ CFSG.pRank 2 (Subgroup.centralizer ({h} : Set K)) := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hK
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  by_cases h1 : h = 1
  · subst h1
    have htop : Subgroup.centralizer ({1} : Set K) = ⊤ := by simp
    rwa [htop]
  · have hrank := CFSG.ProperTwoGeneratedCore.overgroup_involution_centralizer_rank
      (default : Sylow 2 K) ⊤ le_top hK h trivial (orderOf_eq_prime hh h1)
    rwa [top_inf_eq] at hrank

end CFSG.LocalAnalysis.ComponentInitial
