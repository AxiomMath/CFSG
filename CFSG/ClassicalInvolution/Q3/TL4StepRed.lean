module

public import CFSG.ClassicalInvolution.Q3.TL4StepDefs
public import CFSG.ClassicalInvolution.Q3.TL4D1Core
public import CFSG.ClassicalInvolution.Q3.TL4Conn26FinB
public import CFSG.ClassicalInvolution.Q3.TL4OddSecRoute
public import CFSG.ClassicalInvolution.Q3.TL4SepAlphaB
public import CFSG.ClassicalInvolution.Q3.TL4E3Split
public import CFSG.ClassicalInvolution.Q3.TL4E3Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


theorem thmD1StepR_of_core {n : ℕ} (h : D1Core3 (n + 1)) : ThmD1StepR 3 n :=
  thmD1_step h

theorem e3LeafR'_of_parts {n : ℕ} (hZ2 : PlusLeaf TightE3Z2R n) (hS3 : PlusLeaf TightE3S3R n)
    (hE4 : PlusLeaf TightE3E4R n) : PlusLeaf TightE3LeafR' n :=
  fun hA hP => tightE3LeafR'_of_parts (hZ2 hA hP) (hS3 hA hP) (hE4 hA hP)

theorem e3LeafStep_of_R' {n : ℕ} (hα : PlusLeaf TightAlphaLeafR n)
    (h : PlusLeaf TightE3LeafR' n) : E3LeafStep n :=
  fun hA hP => tightE3Leaf_of_R' (hα hA hP) (h hA hP)

theorem connLeafStep_of_R' {n : ℕ} (h : PlusLeaf TightConnLeafR' n) : ConnLeafStep n :=
  fun hA hP => tightConnLeaf_of_R (tightConnLeafR_of_R' (h hA hP))

theorem connLeafR'_of_residuals₇ {n : ℕ} (hD : PlusLeaf TightS26DichR n)
    (h13 : PlusLeaf TightC26_13R n) (hc5 : PlusLeaf TightSec5CliqueR n) (hB : TightBenderEndR)
    (hE4g : PlusLeaf TightE4SecGenR n) (hLC : PlusLeaf TightLambdaCommR n)
    (htri : PlusLeaf TightSecTriangleR n) (h4 : PlusLeaf Thm4RBelow n)
    (hH : PlusLeaf TightHyp51TriR n) (hF : PlusLeaf TightAlphaFrameR n)
    (hNR : PlusLeaf TightSecNoRootR n) : PlusLeaf TightConnLeafR' n :=
  fun hA hP => tightConnLeafR'_of_residuals₇ (hD hA hP) (h13 hA hP) (hc5 hA hP) hB (hE4g hA hP)
    (hLC hA hP) (htri hA hP) (h4 hA hP) (hH hA hP) (hF hA hP) (hNR hA hP)

theorem oddLeafStep_of_E3 {n : ℕ} (hα : PlusLeaf TightAlphaLeafR n)
    (hc : PlusLeaf TightConnLeafR' n) (h : PlusLeaf TightE3LeafR' n)
    (h4 : PlusLeaf Thm4RBelow n) : OddLeafStep n :=
  fun hA hP => tightOddLeaf_of_E3 (hα hA hP) (hc hA hP) (tightSepLeafRα_of_thm4R (h4 hA hP))
    (h hA hP)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
