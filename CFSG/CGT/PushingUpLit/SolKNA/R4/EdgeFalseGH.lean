module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocGlue

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Cert

theorem thm4RBelow_supply_of_gh74 {r n : ℕ} (hr : 4 ≤ r) (hGH : GH74SectionalModels)
    (hT : CIT3Below n → TightBelowR r n → Thm1RTwinBelowR r n) :
    CIT3Below n → TightBelowR r n → TL4.Thm4RBelow r n :=
  fun hA hB => thm4RBelow_of_gh74 hr hGH noQ16E4_holds hA (hT hA hB) hB
    (edgelessClassUniqueR_L2 r) (edgelessClassUniqueR_L3 r) (edgelessClassUniqueR_U3 r)

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4
