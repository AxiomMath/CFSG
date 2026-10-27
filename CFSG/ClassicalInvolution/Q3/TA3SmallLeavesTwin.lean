module

public import CFSG.ClassicalInvolution.Q3.TA3SmallLeavesAll
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3D4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3U4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Blueprint


theorem smallLeaves_of_twin
    (h2M12 : Twin2M12Leaf) (h2Sz8 : Twin2Sz8Leaf)
    (h2An : Twin2AnLeaf) : SmallLeaves :=
  smallLeaves_of_parts smallSimpleLeaf_l3Ne3 smallSimpleLeaf_u3Ne3 smallSimpleLeaf_l4Ne3
    smallSimpleLeaf_u4Ne3 smallSimpleLeaf_g23 smallSimpleLeaf_d43 smallSimpleLeaf_l43
    smallSimpleLeaf_u43 smallSimpleLeaf_l53 h2M12 h2Sz8 h2An

theorem tightSmallBase_of_twin
    (hGH : GH74SectionalModels) (h2M12 : Twin2M12Leaf)
    (h2Sz8 : Twin2Sz8Leaf) (h2An : Twin2AnLeaf) : TightSmallBase :=
  tightSmallBase_of_leaves hGH (smallLeaves_of_twin h2M12 h2Sz8 h2An)

end CFSG.ClassicalInvolution.Q3.TA3
