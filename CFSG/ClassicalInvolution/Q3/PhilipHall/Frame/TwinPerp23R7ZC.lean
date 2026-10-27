module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56Zstar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL



variable {n : ℕ}

theorem p23E7ZC_of_thm4 (hT : Thm4RTwinBelow 3 n) : P23E7ZC n :=
  fun _ _ _ _ _ _ _ _ _ _ _ hc _ _ hZ => R56.p23_zstar_cu hT hc hZ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
