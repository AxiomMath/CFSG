module

public import CFSG.Certificates.Kernel.KDenseP.MW.Mono0
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.MWM cnF cn 24
#kc_select CFSG.KD.MWM onF on 24
#kc_select CFSG.KD.MWM qnF qn 24
#kc_select CFSG.KD.MWM selF sel 24
#kc_select CFSG.KD.MWM xselF xsel 24
#kc_select CFSG.KD.MWM wnF wn 24
#kc_select CFSG.KD.MWM pswF psw 24
#kc_select CFSG.KD.MWM sgXF sgX 24
#kc_select CFSG.KD.MWM sgWF sgW 24
#kc_select CFSG.KD.MWM sgAF sgA 24
#kc_listOf CFSG.KD.MWM keys key 24

namespace CFSG.KD.MWM

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.MWM

end
