module

public import CFSG.Certificates.Kernel.KDenseP.Norton.Mono0
public import CFSG.Certificates.Kernel.KDenseP.Norton.Mono1
public import CFSG.Certificates.Kernel.KDenseP.Norton.Mono2
public import CFSG.Certificates.Kernel.KDenseP.Norton.Mono3
public import CFSG.Certificates.Kernel.KDenseP.Norton.Mono4
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.NRTM cnF cn 313
#kc_select CFSG.KD.NRTM onF on 313
#kc_select CFSG.KD.NRTM qnF qn 313
#kc_select CFSG.KD.NRTM selF sel 313
#kc_select CFSG.KD.NRTM xselF xsel 313
#kc_select CFSG.KD.NRTM wnF wn 313
#kc_select CFSG.KD.NRTM pswF psw 313
#kc_select CFSG.KD.NRTM sgXF sgX 313
#kc_select CFSG.KD.NRTM sgWF sgW 313
#kc_select CFSG.KD.NRTM sgAF sgA 313
#kc_listOf CFSG.KD.NRTM keys key 313

namespace CFSG.KD.NRTM

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.NRTM

end
