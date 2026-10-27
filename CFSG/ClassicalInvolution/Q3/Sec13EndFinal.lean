module

public import CFSG.ClassicalInvolution.Q3.Sec13EndS4
public import CFSG.ClassicalInvolution.Q3.Sec13EndWyl

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

section FrameCert


theorem dLeafEnd_three (IH : ℕ → Prop) : DLeafEnd 3 IH :=
  dLeafEnd_three_of_branches endBranchS4 endBranchWyl IH

end FrameCert

end CFSG.ClassicalInvolution.Q3.Sec13
