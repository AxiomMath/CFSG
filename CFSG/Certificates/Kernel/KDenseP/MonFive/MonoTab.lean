module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Mono0
public import CFSG.Certificates.Kernel.KDenseP.MonFive.Mono1
public import CFSG.Certificates.Kernel.KDenseP.MonFive.Mono2
public import CFSG.Certificates.Kernel.KDenseP.MonFive.Mono3
public import CFSG.Certificates.Kernel.KDenseP.MonFive.Mono4
public import CFSG.Certificates.Kernel.KDenseP.MonFive.Mono5
public import CFSG.Certificates.Kernel.KDenseP.MonFive.Mono6
public import CFSG.Certificates.Kernel.KDenseP.MonFive.Mono7
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.M5RM cnF cn 1488
#kc_select CFSG.KD.M5RM onF on 1488
#kc_select CFSG.KD.M5RM qnF qn 1488
#kc_select CFSG.KD.M5RM selF sel 1488
#kc_select CFSG.KD.M5RM xselF xsel 1488
#kc_select CFSG.KD.M5RM wnF wn 1488
#kc_select CFSG.KD.M5RM pswF psw 1488
#kc_select CFSG.KD.M5RM sgXF sgX 1488
#kc_select CFSG.KD.M5RM sgWF sgW 1488
#kc_select CFSG.KD.M5RM sgAF sgA 1488
#kc_listOf CFSG.KD.M5RM keys key 1488

namespace CFSG.KD.M5RM

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.M5RM

end
