module

public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoG0
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoG1
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoG2
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoG3
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoG4
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoG5
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoG6
public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoG7
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.AXM cnF cn 2663
#kc_select CFSG.KD.AXM onF on 2663
#kc_select CFSG.KD.AXM qnF qn 2663
#kc_select CFSG.KD.AXM selF sel 2663
#kc_select CFSG.KD.AXM xselF xsel 2663
#kc_select CFSG.KD.AXM wnF wn 2663
#kc_select CFSG.KD.AXM pswF psw 2663
#kc_select CFSG.KD.AXM sgXF sgX 2663
#kc_select CFSG.KD.AXM sgWF sgW 2663
#kc_select CFSG.KD.AXM sgAF sgA 2663
#kc_listOf CFSG.KD.AXM keys key 2663

namespace CFSG.KD.AXM

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.AXM

end
