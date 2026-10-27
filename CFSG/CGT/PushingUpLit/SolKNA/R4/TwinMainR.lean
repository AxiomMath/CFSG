module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF14
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G8
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestGH
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafRest3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylCent
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VFinal

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

section Main

structure TwinMainInputsR : Prop where
  leafRest3 : TwinLeaf.TwinLeafRest3

theorem thm4TwinSupplyR_of_mainInputs (hGH : GH74SectionalModels) (_I : TwinMainInputsR) :
    ∀ r : ℕ, 4 ≤ r → ∀ n, Thm4TwinSupplyR r n :=
  thm4TwinSupplyR_all_of_gh74' hGH

theorem twinThmER_of_mainInputs (hGH : GH74SectionalModels) (I : TwinMainInputsR) :
    ∀ r : ℕ, 4 ≤ r → ∀ n, TwinThmER r n :=
  fun r hr n => ThmE.twinThmER_of_inputs hr noQ16E4_holds (ThmE.extendR_of_four_le hr n)
    (thm4TwinSupplyR_of_mainInputs hGH I r hr n)

theorem c25_6R_of_supply {r n : ℕ} (hr : 4 ≤ r) (h4 : Thm4TwinSupplyR r n) : C25_6R r n := by
  intro Y _ _ R S t hP
  exact c25_6R_of_below hr noQ16E4_holds (h4 hP.core.below hP.core.tbelow hP.core.twinBelow)
    hP.core.twinBelow Y R S t hP

theorem twinCorePerpR_of_mainInputs (hGH : GH74SectionalModels) (I : TwinMainInputsR) {r : ℕ}
    (hr : 4 ≤ r) (n : ℕ) (hL : LowerTwinR r n) : TwinCorePerpR r n :=
  twinCorePerpR_of_inputs (TwinSmall.twinPerpSmallR_of_list (smallListR_of_gh74 hGH) hr n
      (TwinLeaf.twinLeavesR_of_rest2 hr n (TwinLeaf.twinLeafRest2_of_rest3 I.leafRest3)))
    (twinPerpV3R_of_thmE hr noQ16E4_holds (thm4TwinSupplyR_of_mainInputs hGH I r hr n)
      (Perp22.thmER_of_twinThmER (twinThmER_of_mainInputs hGH I r hr n)) (Perp22Rest.threeTwinsExclR_of_gh74 hGH hr n
        (TwinSocF4.model163R_of_socF4 (TwinSocF4.socF4L3_holds r) (TwinSocF4.socF4U3_holds r))) (Perp22Wyl.wylD4ExclR_of_thmE hr noQ16E4_holds (twinThmER_of_mainInputs hGH I r hr n)
        (thm4TwinSupplyR_of_mainInputs hGH I r hr n)))
    (Perp23.Three.twinPerp233R_of_thmE hr (twinThmER_of_mainInputs hGH I r hr n)
      (thm4TwinSupplyR_of_mainInputs hGH I r hr n))
    (Perp24.twinPerp24R_of_triangleHyp51R hr (twinThmER_of_mainInputs hGH I r hr n)
      (Perp23.Three.twinPerp233R_of_thmE hr (twinThmER_of_mainInputs hGH I r hr n)
        (thm4TwinSupplyR_of_mainInputs hGH I r hr n)) (Perp24.triangleHyp51R_of_vertexEdgeless noQ16E4_holds
        (TwinSocF4.vertexEdgelessExclR_holds_of_gh74 hGH hr n)))
    (twinPerp25AR_of_inputs (c25_6R_of_supply hr (thm4TwinSupplyR_of_mainInputs hGH I r hr n))
      (C2516.c25_16invR_of_lowerTwin hr noQ16E4_holds
        (c25_6R_of_supply hr (thm4TwinSupplyR_of_mainInputs hGH I r hr n)) hL (C2516.twinCentral4_holds n)))

theorem r4CentTwin_of_mainInputs (hGH : GH74SectionalModels) (I : TwinMainInputsR) :
    ∀ r : ℕ, 4 ≤ r → ∀ n : ℕ, LowerClassR r n → TightCentTwinLiftR r n :=
  r4CentTwin_of_casesL (twinCoreConnR_all noQ16E4_holds (thm4TwinSupplyR_of_mainInputs hGH I))
    (twinCoreDiscPerpR_all noQ16E4_holds (thm4TwinSupplyR_of_mainInputs hGH I) (twinThmER_of_mainInputs hGH I)
      (Disc15.disc15R_all noQ16E4_holds (thm4TwinSupplyR_of_mainInputs hGH I)))
    (fun _ hr n hL => twinCorePerpR_of_mainInputs hGH I hr n hL)

theorem r4TwistAllTwin_of_mainInputs (hGH : GH74SectionalModels) (I : TwinMainInputsR) :
    ∀ r : ℕ, 4 ≤ r → ∀ n : ℕ, LowerClassR r n → TightTwistAllTwinR r n :=
  r4TwistAllTwin_of_casesL (twinCoreConnR_all noQ16E4_holds (thm4TwinSupplyR_of_mainInputs hGH I))
    (twinCoreDiscPerpR_all noQ16E4_holds (thm4TwinSupplyR_of_mainInputs hGH I) (twinThmER_of_mainInputs hGH I)
      (Disc15.disc15R_all noQ16E4_holds (thm4TwinSupplyR_of_mainInputs hGH I)))
    (fun _ hr n hL => twinCorePerpR_of_mainInputs hGH I hr n hL)

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4
