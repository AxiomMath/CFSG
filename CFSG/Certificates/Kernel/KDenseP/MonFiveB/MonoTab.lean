module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Mono0
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Mono1
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Mono2
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Mono3
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Mono4
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Mono5
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Mono6
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Mono7
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.M5BM cnF cn 561
#kc_select CFSG.KD.M5BM onF on 561
#kc_select CFSG.KD.M5BM qnF qn 561
#kc_select CFSG.KD.M5BM selF sel 561
#kc_select CFSG.KD.M5BM xselF xsel 561
#kc_select CFSG.KD.M5BM wnF wn 561
#kc_select CFSG.KD.M5BM pswF psw 561
#kc_select CFSG.KD.M5BM sgXF sgX 561
#kc_select CFSG.KD.M5BM sgWF sgW 561
#kc_select CFSG.KD.M5BM sgAF sgA 561
#kc_listOf CFSG.KD.M5BM keys key 561

namespace CFSG.KD.M5BM

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.M5BM

end
