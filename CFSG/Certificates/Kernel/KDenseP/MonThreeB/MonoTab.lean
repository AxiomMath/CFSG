module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Mono0
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Mono1
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Mono2
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Mono3
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Mono4
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Mono5
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.M3BM cnF cn 415
#kc_select CFSG.KD.M3BM onF on 415
#kc_select CFSG.KD.M3BM qnF qn 415
#kc_select CFSG.KD.M3BM selF sel 415
#kc_select CFSG.KD.M3BM xselF xsel 415
#kc_select CFSG.KD.M3BM wnF wn 415
#kc_select CFSG.KD.M3BM pswF psw 415
#kc_select CFSG.KD.M3BM sgXF sgX 415
#kc_select CFSG.KD.M3BM sgWF sgW 415
#kc_select CFSG.KD.M3BM sgAF sgA 415
#kc_listOf CFSG.KD.M3BM keys key 415

namespace CFSG.KD.M3BM

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.M3BM

end
