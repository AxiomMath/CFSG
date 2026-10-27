module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3F4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3F5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Lem77

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3b


theorem tightE3S3R_of_frame_facts {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n)
    (hSec : TightE3S3Sec163R r n) (hGen : TightSecGenS3R r n) : TightE3S3R r n := by
  intro Y _ _ R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge hμ
  have hF : E3FrameR r n R S t J u := ⟨hL, hcn, hsp, hα, hJ, hu⟩
  have hT4 : Thm4RBelow r n := h4 hL.below hL.tbelow
  by_contra hnE2
  have h163 := hSec Y R S t J u hF htu ht Sb hex hedge hμ hnE2
  obtain ⟨L, hLπ, hLs, hLn⟩ := hF.exists_pick hedge hμ
  have hB := hF.omegaNbr_ne_of_gen hGen htu ht Sb hex hedge hnE2 h163 hLπ hLs hLn
  have hc := hF.cent_of_notBeta htu ht h163 hLπ hLs hB hLn
  obtain ⟨g, Sd, S', R', T, W, hgJ, -, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hnO2 := hF.not_secInO2' htu ht hnE2 hLπ hc hcore
  have h77 := secInO2_of_four_le hr hT4 hL.tbelow hNo hs
  rw [hfam, hcore] at h77
  exact hnO2 h77

end Cit3b

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
