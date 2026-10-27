module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallParts
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinFinalR

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Induction

theorem tightBelowR_all_of_lowerClass (h3 : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n)
    (htw : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerClassR r n → TightTwistAllTwinR r n)
    (hsb : ∀ r : ℕ, 4 ≤ r → TightSmallBaseR r) (hedge : ∀ r : ℕ, 4 ≤ r → ∀ n, TightLargeEdgeSR r n)
    (hlift : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerClassR r n → TightEdgeFalseSR r n)
    (hcent : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerClassR r n → TightCentTwinLiftR r n) :
    ∀ r : ℕ, 4 ≤ r → ∀ N, CIT3Below N → TightBelowR r N := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    have hL : ∀ n, CIT3Below n → LowerClassR r n := fun n hA =>
      ⟨fun r' h1 h2 => ih r' h2 h1 n hA, h3 n hA⟩
    exact tightBelowR_of_parts hr (fun n hA hb => htw r hr n (hL n hA) hA hb) (hsb r hr)
      (hedge r hr) (fun n hA hb => hlift r hr n (hL n hA) hA hb)
      (fun n hA hb => hcent r hr n (hL n hA) hA hb)

theorem tightR4_of_lowerClass (h3 : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n)
    (htw : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerClassR r n → TightTwistAllTwinR r n)
    (hsb : ∀ r : ℕ, 4 ≤ r → TightSmallBaseR r) (hedge : ∀ r : ℕ, 4 ≤ r → ∀ n, TightLargeEdgeSR r n)
    (hlift : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerClassR r n → TightEdgeFalseSR r n)
    (hcent : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerClassR r n → TightCentTwinLiftR r n) : TightR4 :=
  tightR4_of_below (tightBelowR_all_of_lowerClass h3 htw hsb hedge hlift hcent) hedge

end Induction

section Assembly

theorem tightR4_of_gh74
    (hGH : GH74SectionalModels)
    (h3 : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n)
    (hlift : ∀ r : ℕ, 4 ≤ r → ∀ n, LowerClassR r n → TightEdgeFalseSR r n) : TightR4 :=
  tightR4_of_lowerClass h3 (r4TwistAllTwin_of_mainInputs hGH twinMainInputsR_holds)
    (fun r hr =>
      let ⟨hM11, hM12, hL33, hU33, hG23, hD43, hL53, hP43, hT⟩ := r4SmallLeaves_cond hr
      tightSmallBaseR_of_parts r hGH hM11 hM12 hL33 hU33 hG23 hD43 hL53 hP43 (hT hGH))
    (fun _ hr n => tightLargeEdgeSR_holds hr n) hlift
    (r4CentTwin_of_mainInputs hGH twinMainInputsR_holds)

end Assembly

end CFSG.CGT.PushingUpLit.SolKNA.R4
