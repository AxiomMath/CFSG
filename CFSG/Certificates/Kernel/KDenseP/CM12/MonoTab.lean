module

public import CFSG.Certificates.Kernel.KDenseP.CM12.Mono0
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.CM12M cnF cn 22
#kc_select CFSG.KD.CM12M onF on 22
#kc_select CFSG.KD.CM12M qnF qn 22
#kc_select CFSG.KD.CM12M selF sel 22
#kc_select CFSG.KD.CM12M xselF xsel 22
#kc_select CFSG.KD.CM12M wnF wn 22
#kc_select CFSG.KD.CM12M pswF psw 22
#kc_select CFSG.KD.CM12M sgXF sgX 22
#kc_select CFSG.KD.CM12M sgWF sgW 22
#kc_select CFSG.KD.CM12M sgAF sgA 22
#kc_listOf CFSG.KD.CM12M keys key 22

namespace CFSG.KD.CM12M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.CM12M

end
