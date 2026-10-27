module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10PrimGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10BlkGen
public import CFSG.ClassicalInvolution.Q3.TL3C1
public import CFSG.ClassicalInvolution.Q3.TL3T1

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThinPf10

theorem aeBlocks_ge_nine {n : ℕ} (hn : 9 ≤ n) : AEBlocks' n :=
  aeBlocks_of_prim' (by omega) (Or.inr hn) (fourSetPrim_ge_nine hn)

end TwinThinPf10

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
