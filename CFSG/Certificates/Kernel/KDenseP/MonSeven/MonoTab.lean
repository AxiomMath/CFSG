module

public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono0
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono1
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono2
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono3
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono4
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono5
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Mono6
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.M7M cnF cn 638
#kc_select CFSG.KD.M7M onF on 638
#kc_select CFSG.KD.M7M qnF qn 638
#kc_select CFSG.KD.M7M selF sel 638
#kc_select CFSG.KD.M7M xselF xsel 638
#kc_select CFSG.KD.M7M wnF wn 638
#kc_select CFSG.KD.M7M pswF psw 638
#kc_select CFSG.KD.M7M sgXF sgX 638
#kc_select CFSG.KD.M7M sgWF sgW 638
#kc_select CFSG.KD.M7M sgAF sgA 638
#kc_listOf CFSG.KD.M7M keys key 638

namespace CFSG.KD.M7M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.M7M

end
