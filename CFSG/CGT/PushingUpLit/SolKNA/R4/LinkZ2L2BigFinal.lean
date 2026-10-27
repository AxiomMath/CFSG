module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigChoice
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigS7
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX10

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W

section Cit3


variable {r n : ℕ}

theorem z2BigChoiceB_of_split (hSplit : Z2BigSplit r n) : Z2BigChoiceB r n :=
  fun hr Y _ _ R S t J u R₀ T₀ P hs hall hno =>
    hs.exists_choiceB hr hSplit hall hno (hs.exists_sylow_conj_le_actAut_image_linkGrp hr)

theorem z2BigChoiceB_holds (r n : ℕ) : Z2BigChoiceB r n :=
  z2BigChoiceB_of_split (z2BigSplit_holds r n)

end Cit3

section Cert


variable {r n : ℕ}

theorem tightLinkZ2L2BigR_of_four_le (hr : 4 ≤ r)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) (hNo : NoQ16E4) :
    TightLinkZ2L2BigR r n :=
  tightLinkZ2L2BigR_of_inputs hr h4 hNo (z2BigXPlusA_holds r n) (z2BigSplit_holds r n)
    (z2BigChoiceB_holds r n)

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
