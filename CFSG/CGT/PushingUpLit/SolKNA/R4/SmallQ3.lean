module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3M11
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3M12
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3L33
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3U33
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3PSp43
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Lie
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Twin

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 CFSG.Blueprint

theorem smallLeavesR4_holds
    {r : ℕ} (hr : 4 ≤ r) :
    SmallLeafR r TA3.SmallM11 ∧ SmallLeafR r TA3.SmallM12 ∧
      SmallLeafR r (fun F _ => LieModel F .PSL 3 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .PSU 3 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .G2 0 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .trialityD4 0 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .PSL 5 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .PSp 2 3 1) :=
  ⟨smallLeafR_m11 hr, smallLeafR_m12 hr, smallLeafR_l33 hr, smallLeafR_u33 hr, smallLeafR_g23 hr,
    smallLeafR_d43 hr, smallLeafR_l53 hr, smallLeafR_psp43 hr⟩

theorem r4SmallLeaves_cond
    {r : ℕ} (hr : 4 ≤ r) :
    SmallLeafR r TA3.SmallM11 ∧ SmallLeafR r TA3.SmallM12 ∧
      SmallLeafR r (fun F _ => LieModel F .PSL 3 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .PSU 3 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .G2 0 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .trialityD4 0 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .PSL 5 3 1) ∧
      SmallLeafR r (fun F _ => LieModel F .PSp 2 3 1) ∧
      (GH74SectionalModels → NoCentralTwinR r) :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := smallLeavesR4_holds hr
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun hGH => noCentralTwinR_of_gh74 hGH hr⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
