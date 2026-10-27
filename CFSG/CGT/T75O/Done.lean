module

public import CFSG.CGT.T75O.Final
public import CFSG.CGT.T75O.J2
public import CFSG.CGT.T75O.U33
public import CFSG.CGT.T75O.Hex

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.CGT.T75G CFSG.CGT.T75E


theorem sec56CorB_of_listWC (hL : ListWCIdentification) : Sec56CorB := by
  intro G _ T T₁ hy hS hI hnab h2 hR' hcard hplus hnc
  have c : Cfg56 T T₁ := ⟨hy, hS, hI, hnab, h2, hR', hcard, hplus, hnc⟩
  by_cases hJ : NativeSporadic.IsSporadic G .J2
  · exact sec56_j2_excl G T T₁ c G ⟨MulEquiv.refl G⟩ hJ
  by_cases hU : LieModel G .PSU 3 3 1
  · exact sec56_u33_excl G T T₁ c G ⟨MulEquiv.refl G⟩ hU
  obtain ⟨a, ha, ha1⟩ := c.exists_mem_secA_ne_one
  obtain ⟨A₀, P, P', S, h23⟩ := c.exists_setup hL hJ hU ha ha1
  exact c.false_of_setup S h23

end CFSG.CGT.T75O
