module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.E3Z2Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3L2Gen
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Main

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TL4

section Cert


variable {r n : ℕ}

theorem tightE3Z2R_of_four_le (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) (hG : GH74SectionalModels)
    (h6 : ∀ m, TightLargeEdgeSR r m) : TightE3Z2R r n :=
  tightE3Z2R_of_frame_facts hr hNo h4
    (fun hA hB => tightS26DichR_of_four_le hr hNo hG h6 (h4 hA hB) hA hB)
    (tightE3Z2Sec163R_of_four_le hr (smallListR_of_gh74 hG) (noDatumOtherR_holds r) h6
      (TwinSocF4.model163R_of_socF4 (TwinSocF4.socF4L3_holds r) (TwinSocF4.socF4U3_holds r)))
    (tightSecGenS3R_of_four_le hr (smallListR_of_gh74 hG) (noDatumOtherR_holds r) h6
      (l2GenR_holds r))

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
