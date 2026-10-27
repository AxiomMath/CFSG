module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5G2D4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TA3LeafL2
public import CFSG.ClassicalInvolution.Q3.TA3LeafTwistedG2
public import CFSG.ClassicalInvolution.Q3.TA3LeafPSp4All
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSub
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallM11
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallM12
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallL33
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallU33

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Blueprint

theorem smallLeaves_of_parts
    (hL3 : SmallSimpleLeaf SmallL3Ne3)
    (hU3 : SmallSimpleLeaf SmallU3Ne3) (hL4 : SmallSimpleLeaf SmallL4Ne3)
    (hU4 : SmallSimpleLeaf SmallU4Ne3) (hG23 : SmallSimpleLeaf fun F _ => LieModel F .G2 0 3 1)
    (hD43 : SmallSimpleLeaf fun F _ => LieModel F .trialityD4 0 3 1)
    (hL43 : SmallSimpleLeaf fun F _ => LieModel F .PSL 4 3 1)
    (hU43 : SmallSimpleLeaf fun F _ => LieModel F .PSU 4 3 1)
    (hL53 : SmallSimpleLeaf fun F _ => LieModel F .PSL 5 3 1) (h2M12 : Twin2M12Leaf)
    (h2Sz8 : Twin2Sz8Leaf) (h2An : Twin2AnLeaf) : SmallLeaves where
  m11 := smallSimpleLeaf_m11_of_check
  m12 := smallSimpleLeaf_m12_of_check
  l2 := smallSimpleLeaf_l2
  l3 := SmallSimpleLeaf.l3_of_split smallSimpleLeaf_l33_of_check hL3
  u3 := SmallSimpleLeaf.u3_of_split smallSimpleLeaf_u33_of_check hU3
  g2 := SmallSimpleLeaf.g2_of_split hG23 smallSimpleLeaf_g2Ne3
  d4 := SmallSimpleLeaf.d4_of_split hD43 smallSimpleLeaf_d4Ne3
  psp4 := smallSimpleLeaf_psp4
  twistedG2 := smallSimpleLeaf_twistedG2
  l4 := SmallSimpleLeaf.l4_of_split hL43 hL4
  u4 := SmallSimpleLeaf.u4_of_split hU43 hU4
  l5 := SmallSimpleLeaf.l5_of_split hL53 smallSimpleLeaf_l5Ne3
  u5 := smallSimpleLeaf_u5
  twin := smallTwinLeaf_of_sub_leaves h2M12 h2Sz8 h2An

end CFSG.ClassicalInvolution.Q3.TA3
