module

public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono0
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono1
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono2
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono3
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono4
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono5
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono6
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono7
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.M7M cnF cn 680
#kc_select CFSG.KD.M7M onF on 680
#kc_select CFSG.KD.M7M qnF qn 680
#kc_select CFSG.KD.M7M selF sel 680
#kc_select CFSG.KD.M7M xselF xsel 680
#kc_select CFSG.KD.M7M wnF wn 680
#kc_select CFSG.KD.M7M pswF psw 680
#kc_select CFSG.KD.M7M sgXF sgX 680
#kc_select CFSG.KD.M7M sgWF sgW 680
#kc_select CFSG.KD.M7M sgAF sgA 680
#kc_listOf CFSG.KD.M7M keys key 680

namespace CFSG.KD.M7M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.M7M

end
