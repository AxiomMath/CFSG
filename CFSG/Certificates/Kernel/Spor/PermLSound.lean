module

public import Certificates.Data.Kernel.Spor.PermL
public import Certificates.Data.CFSGNative.ONSchreier.Compact
import CFSG.Certificates.Kernel.Spor.PermLProved

public section

namespace CFSG.KS.PermL

theorem permLK_sound {n : Nat} {a : Array Nat} (h : permLK n a.toList = true) :
    a.size = n ∧
      CFSG.ONSchreier.Native.pisInv n a (CFSG.ONSchreier.Native.pinvCand n a) = true :=
  permLK_sound_proved h

end CFSG.KS.PermL

end
