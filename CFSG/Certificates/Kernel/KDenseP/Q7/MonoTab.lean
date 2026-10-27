module

public import CFSG.Certificates.Kernel.KDenseP.Q7.Mono0
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.Q7M cnF cn 8
#kc_select CFSG.KD.Q7M onF on 8
#kc_select CFSG.KD.Q7M qnF qn 8
#kc_select CFSG.KD.Q7M selF sel 8
#kc_select CFSG.KD.Q7M xselF xsel 8
#kc_select CFSG.KD.Q7M wnF wn 8
#kc_select CFSG.KD.Q7M pswF psw 8
#kc_select CFSG.KD.Q7M sgXF sgX 8
#kc_select CFSG.KD.Q7M sgWF sgW 8
#kc_select CFSG.KD.Q7M sgAF sgA 8
#kc_listOf CFSG.KD.Q7M keys key 8

namespace CFSG.KD.Q7M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.Q7M

end
