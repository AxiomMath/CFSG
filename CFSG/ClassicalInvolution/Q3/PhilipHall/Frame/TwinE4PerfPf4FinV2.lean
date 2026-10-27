module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf4Om

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

set_option linter.unusedSectionVars false

open TwinE4Perf in
theorem fin3ActsModels_of_certs₂ : Fin3ActsModels :=
  fin3ActsModels_of_om TwinE4O8.fin3ActsOm_of_certs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
