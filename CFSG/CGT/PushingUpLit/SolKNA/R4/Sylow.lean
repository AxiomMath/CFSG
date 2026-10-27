module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Core
public import CFSG.CGT.PushingUpLit.SolKNA.R4.Z2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

theorem sylowPartsR_holds (r : ℕ) : SylowPartsR r where
  bundle := by
    intro G _ _ R S t hd hq he hn T hT hTG
    exact exists_stdR_of_sylowCase hd hq he hn hT hTG
  w69 := by
    intro G _ _ R S t T h
    exact h.exists_w69
  muZ2OrS3 := by
    intro G _ _ R S t T h W hW
    exact h.muZ2OrS3 hW
  not_muIsoZ2 := by
    intro G _ _ _ hnab hB3 R S t T h W hW
    exact StdR.not_muIsoZ2 hnab hB3 h hW
  not_allTypeTwo := by
    intro G _ _ R S t T h W hW hS3
    exact h.not_allTypeTwo_of_muIsoS3 hW hS3
  e2_of_core := by
    intro h11b G _ _ _ hnab R S t T h hmu
    exact StdR.tightE2Prime_of_coreS h11b hnab h hmu

end CFSG.CGT.PushingUpLit.SolKNA.R4
