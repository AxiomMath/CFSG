module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdge
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeThm6
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeVac
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConn

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin

section SmallList

theorem smallListR_of_gh74 (hGH : GH74SectionalModels) : SmallListR :=
  fun F _ _ _ hnab hP => smallList hGH F hnab hP

end SmallList

section Cert



theorem thm4TwinEdgelessModelR_of_gh74 {r n : ℕ} (hr : 4 ≤ r) (hGH : GH74SectionalModels)
    (h4 : NoQ16E4) (hA : CIT3Below n) (hT : Thm1RTwinBelowR r n) (hB : TightBelowR r n)
    (hL2 : EdgelessClassUniqueR r SmallL2) (hL3 : EdgelessClassUniqueR r SmallL3Ne3)
    (hU3 : EdgelessClassUniqueR r SmallU3Ne3) : Thm4TwinEdgelessModelR r n :=
  thm4TwinEdgelessModelR_of_classUnique hr h4 hA hT hB (tightLargeEdgeSR_holds hr)
    (smallListR_of_gh74 hGH) (noDatumOtherR_holds r) hL2 hL3 hU3

theorem thm4RTwinBelow_of_gh74 {r n : ℕ} (hr : 4 ≤ r) (hGH : GH74SectionalModels)
    (h4 : NoQ16E4) (hA : CIT3Below n) (hT : Thm1RTwinBelowR r n) (hB : TightBelowR r n)
    (hL2 : EdgelessClassUniqueR r SmallL2) (hL3 : EdgelessClassUniqueR r SmallL3Ne3)
    (hU3 : EdgelessClassUniqueR r SmallU3Ne3) : Thm4RTwinBelow r n :=
  thm4RTwinBelow_of_edgelessModelR hr h4 hT hB
    (thm4TwinEdgelessModelR_of_gh74 hr hGH h4 hA hT hB hL2 hL3 hU3)

theorem thm4RBelow_of_gh74 {r n : ℕ} (hr : 4 ≤ r) (hGH : GH74SectionalModels)
    (h4 : NoQ16E4) (hA : CIT3Below n) (hT : Thm1RTwinBelowR r n) (hB : TightBelowR r n)
    (hL2 : EdgelessClassUniqueR r SmallL2) (hL3 : EdgelessClassUniqueR r SmallL3Ne3)
    (hU3 : EdgelessClassUniqueR r SmallU3Ne3) : TL4.Thm4RBelow r n :=
  thm4RBelow_of_thm4RTwin (thm4RTwinBelow_of_gh74 hr hGH h4 hA hT hB hL2 hL3 hU3)

theorem thm4TwinEdgelessModelR_of_gh74_edgeless {r n : ℕ} (hr : 4 ≤ r)
    (hGH : GH74SectionalModels) (h4 : NoQ16E4) (hA : CIT3Below n) (hT : Thm1RTwinBelowR r n)
    (hB : TightBelowR r n) (hU : EdgelessClassUniqueR r EdgelessFamily) :
    Thm4TwinEdgelessModelR r n :=
  let ⟨h2, h3, h4'⟩ := edgelessClassUniqueR_edgelessFamily_iff.mp hU
  thm4TwinEdgelessModelR_of_gh74 hr hGH h4 hA hT hB h2 h3 h4'

theorem thm4RTwinBelow_of_gh74_edgeless {r n : ℕ} (hr : 4 ≤ r) (hGH : GH74SectionalModels)
    (h4 : NoQ16E4) (hA : CIT3Below n) (hT : Thm1RTwinBelowR r n) (hB : TightBelowR r n)
    (hU : EdgelessClassUniqueR r EdgelessFamily) : Thm4RTwinBelow r n :=
  thm4RTwinBelow_of_edgelessModelR hr h4 hT hB
    (thm4TwinEdgelessModelR_of_gh74_edgeless hr hGH h4 hA hT hB hU)

theorem thm4TwinSupplyR_of_gh74 {r n : ℕ} (hr : 4 ≤ r) (hGH : GH74SectionalModels)
    (h4 : NoQ16E4) (hU : EdgelessClassUniqueR r EdgelessFamily) : Thm4TwinSupplyR r n :=
  fun hA hB hT => thm4RTwinBelow_of_gh74_edgeless hr hGH h4 hA hT hB hU

theorem thm4TwinSupplyR_all_of_gh74 (hGH : GH74SectionalModels) (h4 : NoQ16E4)
    (hU : ∀ r : ℕ, 4 ≤ r → EdgelessClassUniqueR r EdgelessFamily) :
    ∀ r : ℕ, 4 ≤ r → ∀ n, Thm4TwinSupplyR r n :=
  fun r hr _ => thm4TwinSupplyR_of_gh74 hr hGH h4 (hU r hr)

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4
