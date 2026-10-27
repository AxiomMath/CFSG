module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallPSp43

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

theorem smallSimpleLeaf_psp4 :
    SmallSimpleLeaf SmallPSp4 :=
  SmallSimpleLeaf.psp4_of_split smallSimpleLeaf_psp43_of_check smallSimpleLeaf_psp4Ne3

end CFSG.ClassicalInvolution.Q3.TA3
