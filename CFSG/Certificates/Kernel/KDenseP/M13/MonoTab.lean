module

public import CFSG.Certificates.Kernel.KDenseP.M13.Mono0
public import CFSG.Certificates.Kernel.KDenseP.M13.Mono1
public import CFSG.Certificates.Kernel.KDenseP.M13.Mono2
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.M13M cnF cn 79
#kc_select CFSG.KD.M13M onF on 79
#kc_select CFSG.KD.M13M qnF qn 79
#kc_select CFSG.KD.M13M selF sel 79
#kc_select CFSG.KD.M13M xselF xsel 79
#kc_select CFSG.KD.M13M wnF wn 79
#kc_select CFSG.KD.M13M pswF psw 79
#kc_select CFSG.KD.M13M sgXF sgX 79
#kc_select CFSG.KD.M13M sgWF sgW 79
#kc_select CFSG.KD.M13M sgAF sgA 79
#kc_listOf CFSG.KD.M13M keys key 79

namespace CFSG.KD.M13M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.M13M

end
