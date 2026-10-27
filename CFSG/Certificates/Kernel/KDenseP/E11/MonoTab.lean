module

public import CFSG.Certificates.Kernel.KDenseP.E11.Mono0
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.E11M cnF cn 32
#kc_select CFSG.KD.E11M onF on 32
#kc_select CFSG.KD.E11M qnF qn 32
#kc_select CFSG.KD.E11M selF sel 32
#kc_select CFSG.KD.E11M xselF xsel 32
#kc_select CFSG.KD.E11M wnF wn 32
#kc_select CFSG.KD.E11M pswF psw 32
#kc_select CFSG.KD.E11M sgXF sgX 32
#kc_select CFSG.KD.E11M sgWF sgW 32
#kc_select CFSG.KD.E11M sgAF sgA 32
#kc_listOf CFSG.KD.E11M keys key 32

namespace CFSG.KD.E11M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.E11M

end
