module

public import CFSG.Certificates.Kernel.LBindProved

public section

namespace CFSG.KS.Raw

theorem lbindK_sound {L : List Nat} {n w P : Nat} (h : lbindK L n w P = true) :
    L.toArray = unpack n w P :=
  lbindK_sound_proved h

end CFSG.KS.Raw

end
