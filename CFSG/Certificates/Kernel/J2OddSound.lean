
module

public import Certificates.Data.Kernel.J2Odd
import CFSG.Certificates.Kernel.J2Odd.Sound
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.KC.J2Odd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.ComponentClassification.J2Cover
open CFSG.Sporadic.Schreier.Native

theorem oddK_sound {n w m : Nat} {L W : List Nat} (hn : 1 < n)
    (hc : ∀ X ∈ L, canonK n w (mask w) (n * w) X = true) (h : oddK n w m L W = true) :
    oddWitnessOK n m (L.map fun X => arrTable n (unpack n w X)) = true :=
  Pf.oddK_sound' hn hc h

end CFSG.KC.J2Odd

end
