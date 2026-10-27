module

public import Certificates.Data.Kernel.Spor.M11Class
import CFSG.Certificates.Kernel.Spor.PK.M11Class

public section

namespace CFSG.KS.M11Class

open CFSG.KS.M11

theorem pairCntL_class {A Ai B Bi R Ri cap : Nat} {Bl P Lb S SY : List Nat} {XL YL : List (Nat × Nat)}
    (h : classRowOK A Ai B Bi R Ri Bl P Lb S SY XL YL cap = true) :
    pairCntL XL YL = XL.length * rowCnt R Ri YL :=
  CFSG.KS.PK.pairCntL_class' h

end CFSG.KS.M11Class

end
