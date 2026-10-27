module

public import Certificates.Data.Kernel.Spor.Mathieu
import CFSG.Certificates.Kernel.Spor.PK.Mathieu

public section

namespace CFSG.KS.Mathieu

open CFSG.Sporadic.Mathieu.Native

theorem mcheck_sound {n w : Nat} {D : Data} (hD : D.words.size < 2 ^ 31)
    (h : mcheck n w D = true) : check n D = true :=
  CFSG.KS.PK.mcheck_sound' hD h

end CFSG.KS.Mathieu

end
