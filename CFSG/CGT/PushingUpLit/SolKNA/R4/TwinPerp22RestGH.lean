module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22ThmE
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocGlue
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinWToolExtend

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.CGT.PushingUpLit.SolKNA.R4

section Main


theorem threeTwinsExclR_of_gh74 (hGH : GH74SectionalModels) {r : ℕ} (hr : 4 ≤ r) (n : ℕ)
    (hM : Model163R r) : Perp22.ThreeTwinsExclR r n :=
  threeTwinsExclR_of_model163R hr noQ16E4_holds (smallListR_of_gh74 hGH) (noDatumOtherR_holds r)
    (tightLargeEdgeSR_holds hr) hM
    (Perp22.thmER_of_twinThmER
      (ThmE.twinThmER_of_inputs hr noQ16E4_holds (ThmE.extendR_of_four_le hr n)
        (thm4TwinSupplyR_all_of_gh74' hGH r hr n)))

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest
