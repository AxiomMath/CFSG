module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.SmallRanks
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.GH74.Filter

open Blueprint Assembly.LowTwoRank

theorem t_PSL_two_odd : S_PSL_two_odd := fun _ _ _ _ _ hp2 h =>
  SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd h.1.1 hp2 h

theorem t_PSL_two_four : S_PSL_two_four := fun _ _ _ h =>
  (SmallRanks.twoRank_eq_of_statedClassicalModel_PSL_two_two h).le

theorem t_PSL_three_two : S_PSL_three_two := fun G _ _ h =>
  twoRank_le_two_of_lieModel_PSL_two_odd Nat.prime_seven (by norm_num)
    (LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism G
      (lieModel_of_classical (by decide) h))

theorem t_PSU_three_four : S_PSU_three_four := fun _ _ _ h =>
  SmallRanks.twoRank_le_two_of_statedClassicalModel_PSU_three_four h

theorem t_M11 : S_M11 := fun _ _ _ h => twoRank_le_two_of_M11 h

theorem t_iso_L4_two : S_iso_L4_two := fun _ _ h =>
  Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel (lieModel_of_classical (by decide) h)

theorem t_iso_U4_two : S_iso_U4_two := fun _ _ h =>
  Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two h

end CFSG.GH74.Filter
