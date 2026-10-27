module

public import CFSG.Certificates.Kernel.KDenseP.HeSeven.Mono0
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.HE7M cnF cn 34
#kc_select CFSG.KD.HE7M onF on 34
#kc_select CFSG.KD.HE7M qnF qn 34
#kc_select CFSG.KD.HE7M selF sel 34
#kc_select CFSG.KD.HE7M xselF xsel 34
#kc_select CFSG.KD.HE7M wnF wn 34
#kc_select CFSG.KD.HE7M pswF psw 34
#kc_select CFSG.KD.HE7M sgXF sgX 34
#kc_select CFSG.KD.HE7M sgWF sgW 34
#kc_select CFSG.KD.HE7M sgAF sgA 34
#kc_listOf CFSG.KD.HE7M keys key 34

namespace CFSG.KD.HE7M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.HE7M

end
