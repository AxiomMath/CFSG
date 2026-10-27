module

public import CFSG.CGT.PushingUpLit.T2K.Bundle
public import CFSG.CGT.PushingUpLit.T2KR.Asc78FromThreeS

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

structure OpenInputsNonSylow : Prop where
  threeSNonSylow : CFSG.CGT.PushingUpLit.A78.Aschbacher78ThreeSNonSylow
  hall : Asc76Lemma25
  print55 : Print55

theorem OpenInputsNonSylow.toOpenInputs (h : OpenInputsNonSylow) : OpenInputs :=
  ⟨aschbacher78OneGen_of_threeSNonSylow h.threeSNonSylow, h.hall, h.print55⟩

end CFSG.CGT.PushingUpLit.T2K
