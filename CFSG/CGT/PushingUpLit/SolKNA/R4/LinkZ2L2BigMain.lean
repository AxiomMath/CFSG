module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big31
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big35
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big38
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big39
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big40

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W

section Cert




variable {r n : ℕ}

theorem tightLinkZ2L2BigR_of_inputs (hr : 4 ≤ r)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) (hNo : NoQ16E4)
    (hX : Z2BigXPlusA r n) (hSplit : Z2BigSplit r n) (hChoice : Z2BigChoiceB r n) :
    TightLinkZ2L2BigR r n :=
  tightLinkZ2L2BigR_of_props hr hNo h4 (z2BigAdapted_holds r n) C264.z2BigC264One_holds
    (z2BigProp7a_of_hweak_notConj (z2BigHweak_holds r n) (z2BigNotConjTU_holds r n))
    (z2BigProp6a4_of_parts hChoice (z2BigT1_of_xplus hX) (z2BigT2_of_xplus_split hX hSplit)
      (z2BigHweak_holds r n))

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
