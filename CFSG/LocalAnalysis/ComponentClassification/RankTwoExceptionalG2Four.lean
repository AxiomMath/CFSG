module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCover

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup

theorem g2FourOddCenter :
    G2FourOddCenter := by
  intro A _ _ hA hS hodd
  have : Group.IsPerfect A := Group.isPerfect_def.2 hA
  have hker : (QuotientGroup.mk' (center A)).ker = center A := QuotientGroup.ker_mk' _
  have h := CFSG.SectionRank.g2_even_perfect_odd_cover_trivial hS (QuotientGroup.mk' (center A))
    (QuotientGroup.mk'_surjective _) hker.le (by rw [hker]; exact hodd)
  rwa [hker] at h

end CFSG.ComponentClassification.RankTwoExceptional
