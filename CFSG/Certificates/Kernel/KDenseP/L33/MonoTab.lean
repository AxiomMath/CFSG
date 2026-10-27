module

public import CFSG.Certificates.Kernel.KDenseP.L33.Mono0
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.L33M cnF cn 19
#kc_select CFSG.KD.L33M onF on 19
#kc_select CFSG.KD.L33M qnF qn 19
#kc_select CFSG.KD.L33M selF sel 19
#kc_select CFSG.KD.L33M xselF xsel 19
#kc_select CFSG.KD.L33M wnF wn 19
#kc_select CFSG.KD.L33M pswF psw 19
#kc_select CFSG.KD.L33M sgXF sgX 19
#kc_select CFSG.KD.L33M sgWF sgW 19
#kc_select CFSG.KD.L33M sgAF sgA 19
#kc_listOf CFSG.KD.L33M keys key 19

namespace CFSG.KD.L33M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.L33M

end
