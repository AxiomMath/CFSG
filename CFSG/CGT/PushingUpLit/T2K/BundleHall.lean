module

public import CFSG.CGT.PushingUpLit.T2K.BundleSp4
public import CFSG.CGT.PushingUpLit.A78S4.FromCfg

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

structure OpenInputsHall : Prop where
  hall : Asc76Lemma25
  print55 : Print55

theorem OpenInputsHall.toSp4 (h : OpenInputsHall) : OpenInputsSp4 :=
  ⟨CFSG.CGT.PushingUpLit.A78S4.sp4FromCfg, h.hall, h.print55⟩

theorem OpenInputsHall.toNonSylow (h : OpenInputsHall) : OpenInputsNonSylow :=
  h.toSp4.toNonSylow

end CFSG.CGT.PushingUpLit.T2K
