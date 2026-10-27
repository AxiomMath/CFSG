module

public import Certificates.Data.Kernel.SporSch.RuEBfsK
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
import CFSG.Certificates.Kernel.SporSch.RuEBfsProved
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.RuSchreier

theorem ebfsK_sound {Z N0 N1 N0I N1I : Nat} (hz : ruZA = unpack 4060 12 Z)
    (hzc : canonK 4060 12 (mask 12) (4060 * 12) Z = true)
    (h0 : ruNs0A = unpack 4060 12 N0) (h1 : ruNs1A = unpack 4060 12 N1)
    (p0 : permOK 4060 12 (mask 12) (4060 * 12) N0 N0I = true)
    (p1 : permOK 4060 12 (mask 12) (4060 * 12) N1 N1I = true) :
    ruEBFS = (((ebfsK N0 N1 N0I N1I Z).1.map (unpack 4060 12)).toArray,
      (ebfsK N0 N1 N0I N1I Z).2.1.toArray, (ebfsK N0 N1 N0I N1I Z).2.2.toArray) :=
  EbfsGen.inst (ebfsK_sound_gen_proved ru4060Text) hz hzc h0 h1 p0 p1

end CFSG.KS.SporSch

end
