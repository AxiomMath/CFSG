module

public import CFSG.Certificates.Kernel.KDenseP.DenseAlign.Mono0
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.DA7M cnF cn 39
#kc_select CFSG.KD.DA7M onF on 39
#kc_select CFSG.KD.DA7M qnF qn 39
#kc_select CFSG.KD.DA7M selF sel 39
#kc_select CFSG.KD.DA7M xselF xsel 39
#kc_select CFSG.KD.DA7M wnF wn 39
#kc_select CFSG.KD.DA7M pswF psw 39
#kc_select CFSG.KD.DA7M sgXF sgX 39
#kc_select CFSG.KD.DA7M sgWF sgW 39
#kc_select CFSG.KD.DA7M sgAF sgA 39
#kc_listOf CFSG.KD.DA7M keys key 39

namespace CFSG.KD.DA7M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.DA7M

end
