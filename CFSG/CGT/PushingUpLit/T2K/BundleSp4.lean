module

public import CFSG.CGT.PushingUpLit.T2K.BundleNonSylow
public import CFSG.CGT.PushingUpLit.A78.NonSylowData

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

structure OpenInputsSp4 : Prop where
  sp4From : CFSG.CGT.PushingUpLit.A78Sp4.Sp4FromCfg
  hall : Asc76Lemma25
  print55 : Print55

theorem OpenInputsSp4.toNonSylow (h : OpenInputsSp4) : OpenInputsNonSylow :=
  ⟨CFSG.CGT.PushingUpLit.A78.threeSNonSylow_of_sp4 h.sp4From, h.hall, h.print55⟩

end CFSG.CGT.PushingUpLit.T2K
