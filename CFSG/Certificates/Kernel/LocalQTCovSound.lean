module

public import Certificates.Data.Kernel.LocalQT.Cov
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck

import CFSG.Certificates.Kernel.LocalQTCovProved

public section

namespace CFSG.KC.LQT.Cov

open CFSG.QuasithinUnique.Ch1.M22Cover CFSG.KC.LQT.W CFSG.Sporadic.Mathieu

theorem cov_sound (cs : List Char) (H : List (List ℕ)) (nV0 : ℕ) (free0 : List ℕ) {cA cB : ℕ}
    (hA : codeP m22gA = cA) (hB : codeP m22gB = cB) (h : covK 22 cA cB cs H nV0 free0 = true) :
    covCheck (parseData (String.ofList cs)) = true ∧ (parseData (String.ofList cs)).nV = nV0 ∧
      (parseData (String.ofList cs)).free = free0 :=
  cov_sound_proved cs H nV0 free0 hA hB h

end CFSG.KC.LQT.Cov

end
