module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrClosed
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigFinal
public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseGH
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinFinalR

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

section Closed

theorem thm1RTwinBelowR_of_lowerClass
    (hGH : GH74SectionalModels) {r n : ℕ} (hr : 4 ≤ r)
    (hL : LowerClassR r n) : CIT3Below n → TightBelowR r n → Thm1RTwinBelowR r n :=
  fun hA hB => thm1RTwinBelowR_tower
    (twinCoreConnR_all noQ16E4_holds (thm4TwinSupplyR_of_mainInputs hGH twinMainInputsR_holds))
    (twinCoreDiscPerpR_all noQ16E4_holds
      (thm4TwinSupplyR_of_mainInputs hGH twinMainInputsR_holds)
      (twinThmER_of_mainInputs hGH twinMainInputsR_holds)
      (Disc15.disc15R_all noQ16E4_holds
        (thm4TwinSupplyR_of_mainInputs hGH twinMainInputsR_holds)))
    (fun _ hr' m hL' => twinCorePerpR_of_mainInputs hGH twinMainInputsR_holds hr' m hL')
    r hr n hA hB hL

theorem tightEdgeFalseSR_of_lowerClass
    (hGH : GH74SectionalModels) {r n : ℕ} (hr : 4 ≤ r)
    (hL : LowerClassR r n) : TightEdgeFalseSR r n :=
  have h4 := thm4RBelow_supply_of_gh74 hr hGH (thm1RTwinBelowR_of_lowerClass hGH hr hL)
  RonanRes.tightEdgeFalseSR_of_linkZ2L2Big hr noQ16E4_holds h4
    (Z2Big.tightLinkZ2L2BigR_of_four_le hr h4 noQ16E4_holds)

end Closed

end CFSG.CGT.PushingUpLit.SolKNA.R4
