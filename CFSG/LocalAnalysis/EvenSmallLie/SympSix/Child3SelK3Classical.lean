module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3ClassicalU

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup CFSG.Assembly.LowTwoRank

theorem excluded_PSU_three_five : ExcludedLie .PSU 3 5 1 := by
  intro Y _ _ D a J h hL
  have hT : StatedClassicalModel D .PSU 3 5 1 := by
    rcases hL with ⟨-, hc⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩
    · exact hc
    all_goals exact absurd hm (by decide)
  exact false_of_k3 (SelK3Classical.four_dvd_card_centralizer_of_PSU_three_five hT) Y D a J h
    ⟨MulEquiv.refl D⟩

theorem excluded_PSp_two_seven : ExcludedLie .PSp 2 7 1 := by
  intro Y _ _ D a J h hL
  have hT : StatedClassicalModel D .PSp 2 7 1 := by
    rcases hL with ⟨-, hc⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩
    · exact hc
    all_goals exact absurd hm (by decide)
  exact false_of_k3 (SelK3Classical.four_dvd_card_centralizer_of_PSp_two_seven hT) Y D a J h
    ⟨MulEquiv.refl D⟩

theorem classicalExclusions : ClassicalExclusions :=
  ⟨excluded_PSU_three_five, excluded_PSp_two_seven⟩

end CFSG.EvenSmallLie.Child3
