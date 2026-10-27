module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwin
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinOutL4b
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinOutU4b

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

theorem smallTwinLeaf_of_sub_leaves
    (h2M12 : Twin2M12Leaf) (h2Sz8 : Twin2Sz8Leaf) (h2An : Twin2AnLeaf) : SmallTwinLeaf :=
  smallTwinLeaf_of_parts TwinFr.sl4FrameOuterQ8Free_holds TwinFr.su4FrameOuterQ8Free_holds h2M12
    h2Sz8 h2An

end CFSG.ClassicalInvolution.Q3.TA3
