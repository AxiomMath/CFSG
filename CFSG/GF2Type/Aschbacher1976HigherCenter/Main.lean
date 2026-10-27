module

public import CFSG.GF2Type.Aschbacher1976HigherCenter.Input43
public import CFSG.GF2Type.Aschbacher1976HigherCenter.CenterNotWeaklyClosed
public import CFSG.GF2Type.Aschbacher1976HigherCenter.ConjugateCenterExclusion

public section

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

theorem higher_center_case_of_four_three
    (h43 : CyclicFourNotWeaklyClosed) :
    CFSG.Yardstones.M3aba7dc4b8a8.Aschbacher1976HigherCenterCase := by
  unfold CFSG.Yardstones.M3aba7dc4b8a8.Aschbacher1976HigherCenterCase
  intro G _ _ _ z hset hnex hexp
  obtain ⟨B, D, k, u, h⟩ := exists_setup G z hset hnex hexp
  obtain ⟨T, hTY, hT4, hzT, hTcyc⟩ := exists_order_four_subgroup h
  obtain ⟨g, hgM, hgY⟩ :=
    exists_conjugate_center_in_local h hTY hT4 (h43 G z hset T hzT hTcyc hT4)
  exact (false_of_conjugate_center_in_local h hgM hgY).elim

end CFSG.GF2Type.Aschbacher1976HigherCenter
