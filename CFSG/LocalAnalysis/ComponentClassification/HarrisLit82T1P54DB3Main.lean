module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DB3Plus
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DB3Minus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup Assembly.LowTwoRank CFSG.LieType.Universal.Spin

theorem rowDBThree : RowDBThree := by
  constructor
  · intro K _ _ m hK3 hm Y _ _ α hα hk t htZ htn ht2
    have ht1 : t ≠ 1 := fun h => by
      rw [h, map_one, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    exact (DB.rawF3_plus hK3 hm htZ ht1 htn).concl3 (isQuasisimple_spinGroup_quadPlus (by omega))
      hα hk ht2 htZ
  · intro K _ _ m b c hirr hK3 hm Y _ _ α hα hk t htZ htn ht2
    have ht1 : t ≠ 1 := fun h => by
      rw [h, map_one, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    exact (DB.rawF3_minus hK3 hirr hm htZ ht1 htn).concl3
      (isQuasisimple_spinGroup_quadMinus hm hirr) hα hk ht2 htZ

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3
