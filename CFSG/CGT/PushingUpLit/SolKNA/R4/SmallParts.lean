module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallSplit
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4G2D4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4L5U5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4Sp4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4L4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4U4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NoDatum4TwistedG2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallL2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallL3U3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3

theorem smallLeavesR_of_parts (r : ℕ) (hM11 : SmallLeafR r SmallM11)
    (hM12 : SmallLeafR r SmallM12) (hL33 : SmallLeafR r fun F _ => LieModel F .PSL 3 3 1)
    (hU33 : SmallLeafR r fun F _ => LieModel F .PSU 3 3 1)
    (hG23 : SmallLeafR r fun F _ => LieModel F .G2 0 3 1)
    (hD43 : SmallLeafR r fun F _ => LieModel F .trialityD4 0 3 1)
    (hL53 : SmallLeafR r fun F _ => LieModel F .PSL 5 3 1)
    (hP43 : SmallLeafR r fun F _ => LieModel F .PSp 2 3 1) : SmallLeavesR r where
  m11 := hM11
  m12 := hM12
  l2 := smallLeafR_l2 r
  l3 := smallLeafR_l3_of_split hL33 (smallLeafR_l3Ne3 r)
  u3 := smallLeafR_u3_of_split hU33 (smallLeafR_u3Ne3 r)
  g2 := smallLeafR_g2_of_split hG23 smallLeafR_g2Ne3
  d4 := smallLeafR_d4_of_split hD43 smallLeafR_d4Ne3
  psp4 := smallLeafR_psp4_of_split hP43 smallLeafR_psp4Ne3
  twistedG2 := smallLeafR_twistedG2
  l4 := smallLeafR_l4_of_split smallLeafR_l43 smallLeafR_l4Ne3
  u4 := smallLeafR_u4_of_split smallLeafR_u43 smallLeafR_u4Ne3
  l5 := smallLeafR_l5_of_split hL53 smallLeafR_l5Ne3
  u5 := smallLeafR_u5

theorem tightSmallBaseR_of_parts (r : ℕ) (hGH : GH74SectionalModels)
    (hM11 : SmallLeafR r SmallM11) (hM12 : SmallLeafR r SmallM12)
    (hL33 : SmallLeafR r fun F _ => LieModel F .PSL 3 3 1)
    (hU33 : SmallLeafR r fun F _ => LieModel F .PSU 3 3 1)
    (hG23 : SmallLeafR r fun F _ => LieModel F .G2 0 3 1)
    (hD43 : SmallLeafR r fun F _ => LieModel F .trialityD4 0 3 1)
    (hL53 : SmallLeafR r fun F _ => LieModel F .PSL 5 3 1)
    (hP43 : SmallLeafR r fun F _ => LieModel F .PSp 2 3 1) (hT : NoCentralTwinR r) :
    TightSmallBaseR r :=
  tightSmallBaseR_of_leaves hGH (smallLeavesR_of_parts r hM11 hM12 hL33 hU33 hG23 hD43 hL53 hP43) hT

end CFSG.CGT.PushingUpLit.SolKNA.R4
