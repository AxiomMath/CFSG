module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3D4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3

theorem smallLeafR_g23 {r : ℕ} (hr : 4 ≤ r) :
    SmallLeafR r fun F _ => CFSG.Blueprint.LieModel F .G2 0 3 1 := by
  intro Y _ _ _ hnab _ hm R S t hd hc _
  exact absurd (good_g23 hnab hm hd) (not_goodThreeElement_of_four_le hr hd hc.1)

theorem smallLeafR_d43 {r : ℕ} (hr : 4 ≤ r) :
    SmallLeafR r fun F _ => CFSG.Blueprint.LieModel F .trialityD4 0 3 1 := by
  intro Y _ _ _ hnab _ hm R S t hd hc _
  exact absurd (good_d43 hnab hm hd) (not_goodThreeElement_of_four_le hr hd hc.1)

theorem smallLeafR_l53 {r : ℕ} (hr : 4 ≤ r) :
    SmallLeafR r fun F _ => CFSG.Blueprint.LieModel F .PSL 5 3 1 := by
  intro Y _ _ _ hnab _ hm R S t hd hc _
  exact absurd (good_l53 hnab hm hd) (not_goodThreeElement_of_four_le hr hd hc.1)

end CFSG.CGT.PushingUpLit.SolKNA.R4
