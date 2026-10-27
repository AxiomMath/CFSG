module

public import CFSG.Certificates.Kernel.KDenseP.M13.Mono0
public import CFSG.Certificates.Kernel.KDenseP.M13.Mono1
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.M13M cnF cn 76
#kc_select CFSG.KD.M13M onF on 76
#kc_select CFSG.KD.M13M qnF qn 76
#kc_select CFSG.KD.M13M selF sel 76
#kc_select CFSG.KD.M13M xselF xsel 76
#kc_select CFSG.KD.M13M wnF wn 76
#kc_select CFSG.KD.M13M pswF psw 76
#kc_select CFSG.KD.M13M sgXF sgX 76
#kc_select CFSG.KD.M13M sgWF sgW 76
#kc_select CFSG.KD.M13M sgAF sgA 76
#kc_listOf CFSG.KD.M13M keys key 76

namespace CFSG.KD.M13M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.M13M

end
