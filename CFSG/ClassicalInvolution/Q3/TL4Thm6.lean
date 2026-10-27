module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6Asm
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Split
public import CFSG.ClassicalInvolution.Q3.TL4Thm6M11
public import CFSG.ClassicalInvolution.Q3.TL4Thm6PSp43
public import CFSG.ClassicalInvolution.Q3.TL4Thm6L2
public import CFSG.ClassicalInvolution.Q3.TL4Thm6L3
public import CFSG.ClassicalInvolution.Q3.TL4Thm6U3
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Q3
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3D4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3U4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4
public import CFSG.ClassicalInvolution.Q3.TA3LeafTwistedG2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem smallLeaves6_holds : SmallLeaves6 where
  m11 := Thm6.smallSimpleLeaf6_m11
  m12 := SmallSimpleLeaf6.of_exitIdent Thm6.exitIdent_m12
  l2 := SmallSimpleLeaf6.of_exitIdent Thm6.exitIdent_l2
  l3 := SmallSimpleLeaf6.of_split Thm6.split_l3 (SmallSimpleLeaf6.of_exitIdent Thm6.exitIdent_l33)
    (SmallSimpleLeaf6.of_exitIdent Thm6.exitIdent_l3Ne3)
  u3 := SmallSimpleLeaf6.of_split Thm6.split_u3 (SmallSimpleLeaf6.of_exitIdent Thm6.exitIdent_u33)
    (SmallSimpleLeaf6.of_exitIdent Thm6.exitIdent_u3Ne3)
  g2 := SmallSimpleLeaf6.of_split Thm6.split_g2
    (SmallSimpleLeaf6.of_good fun _ _ _ _ hnab hm _ _ _ hd => TA3.good_g23 hnab hm hd)
    (SmallSimpleLeaf6.of_noQ8Datum TA3.noQ8Datum_g2Ne3)
  d4 := SmallSimpleLeaf6.of_split Thm6.split_d4
    (SmallSimpleLeaf6.of_good fun _ _ _ _ hnab hm _ _ _ hd => TA3.good_d43 hnab hm hd)
    (SmallSimpleLeaf6.of_noQ8Datum TA3.noQ8Datum_d4Ne3)
  psp4 := SmallSimpleLeaf6.of_split Thm6.split_psp4 Thm6.smallSimpleLeaf6_psp43
    (SmallSimpleLeaf6.of_noQ8Datum TA3.noQ8Datum_psp4Ne3)
  twistedG2 := SmallSimpleLeaf6.of_noDatum TA3.noDatum_smallTwistedG2
  l4 := SmallSimpleLeaf6.of_split Thm6.split_l4 (SmallSimpleLeaf6.of_noQ8Datum TA3.noQ8Datum_l43)
    (SmallSimpleLeaf6.of_noQ8Datum TA3.noQ8Datum_l4Ne3)
  u4 := SmallSimpleLeaf6.of_split Thm6.split_u4 (SmallSimpleLeaf6.of_noQ8Datum TA3.noQ8Datum_u43)
    (SmallSimpleLeaf6.of_noQ8Datum TA3.noQ8Datum_u4Ne3)
  l5 := SmallSimpleLeaf6.of_split Thm6.split_l5
    (SmallSimpleLeaf6.of_good fun _ _ _ _ hnab hm _ _ _ hd => TA3.good_l53 hnab hm hd)
    (SmallSimpleLeaf6.of_noQ8Datum TA3.noQ8Datum_l5Ne3)
  u5 := SmallSimpleLeaf6.of_noQ8Datum TA3.noQ8Datum_u5

theorem thm6StepR_three (hGH : GH74SectionalModels) (n : ℕ) : Thm6StepR 3 n :=
  thm6StepR_three_of_leaves hGH smallLeaves6_holds n

end CFSG.ClassicalInvolution.Q3.TL4
