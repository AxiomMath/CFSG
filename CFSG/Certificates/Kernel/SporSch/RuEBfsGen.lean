module

public import Certificates.Data.Kernel.SporSch.RuEBfsK
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
import CFSG.Certificates.Kernel.Common.Generalize

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.RuSchreier

#kc_generalize EbfsGen (t : String) using [CFSG.Sporadic.RuSchreier.ru4060Text ↦ t] :
  ∀ {Z N0 N1 N0I N1I : Nat}, ruZA = unpack 4060 12 Z →
    canonK 4060 12 (mask 12) (4060 * 12) Z = true →
    ruNs0A = unpack 4060 12 N0 → ruNs1A = unpack 4060 12 N1 →
    permOK 4060 12 (mask 12) (4060 * 12) N0 N0I = true →
    permOK 4060 12 (mask 12) (4060 * 12) N1 N1I = true →
    ruEBFS = (((ebfsK N0 N1 N0I N1I Z).1.map (unpack 4060 12)).toArray,
      (ebfsK N0 N1 N0I N1I Z).2.1.toArray, (ebfsK N0 N1 N0I N1I Z).2.2.toArray)

end CFSG.KS.SporSch

end
