module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3L2Gen
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Main

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TL4

section Cert


theorem tightE3S3R_of_four_le {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) (hG : GH74SectionalModels)
    (h6 : ∀ m, TightLargeEdgeSR r m) : TightE3S3R r n :=
  tightE3S3R_of_frame_facts hr hNo h4
    (tightE3S3Sec163R_of_four_le hr (smallListR_of_gh74 hG) (noDatumOtherR_holds r) h6
      (TwinSocF4.model163R_of_socF4 (TwinSocF4.socF4L3_holds r) (TwinSocF4.socF4U3_holds r)))
    (tightSecGenS3R_of_four_le hr (smallListR_of_gh74 hG) (noDatumOtherR_holds r) h6 (l2GenR_holds r))

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
