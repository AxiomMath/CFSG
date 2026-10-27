module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Final
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResLeaves
public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalse
public import CFSG.ClassicalInvolution.Q3.TL4Conn26FinB
public import CFSG.ClassicalInvolution.Q3.TL4GLinkAlpha

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

section Cert


variable {r n : ℕ}

theorem tightConnLeafR'_of_four_le_five (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) (hG : GH74SectionalModels)
    (h6 : ∀ m, TightLargeEdgeSR r m) : TightConnLeafR' r n := by
  intro Y _ _ R S t hL
  have hT4 := h4 hL.below hL.tbelow
  exact tightConnLeafR'_of_residuals₇
    (tightS26DichR_of_four_le hr hNo hG h6 hT4 hL.below hL.tbelow)
    (tightC26_13R_of_four_le hr hNo h4)
    (tightSec5CliqueR_of_four_le hr hNo hT4 hL.tbelow) tightBenderEndR
    (tightE4SecGenR_of_four_le hr hT4 hL.tbelow hNo)
    (tightLambdaCommR_of_four_le hr hT4 hL.tbelow hNo)
    (tightSecTriangleR_of_four_le hr hT4 hL.tbelow hNo) hT4
    (tightHyp51TriR_of_four_le hr hNo h4) (tightAlphaFrameR_of_four_le hr hNo h4)
    (tightSecNoRootR_of_four_le hr hT4 hL.tbelow hNo) Y R S t hL

theorem tightEdgeFalseSR_of_two_residuals (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) (hG : GH74SectionalModels)
    (hnb : TightAlphaNoNbrR r n) (hZ2 : TightE3Z2R r n) : TightEdgeFalseSR r n :=
  tightEdgeFalseSR_of_main hr
    (tightAlphaLeafR_of_graphA (tightHyp51TriR_of_four_le hr hNo h4)
      (tightGraphLinkAR_of_four_le hr hNo h4) hnb)
    (tightConnLeafR'_of_four_le_five hr hNo h4 hG fun m => tightLargeEdgeSR_holds hr m) h4
    (tightE3LeafR'_of_parts hZ2
      (tightE3S3R_of_four_le hr hNo h4 hG fun m => tightLargeEdgeSR_holds hr m)
      (tightE3E4R_of_four_le hr hNo))

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
