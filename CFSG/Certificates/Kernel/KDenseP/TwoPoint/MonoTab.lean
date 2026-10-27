module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono0
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono1
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono2
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono3
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono4
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono5
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono6
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono7
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono8
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono9
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono10
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono11
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono12
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono13
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono14
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono15
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono16
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono17
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono18
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono19
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono20
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono21
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono22
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Mono23
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.TPM cnF cn 192
#kc_select CFSG.KD.TPM onF on 192
#kc_select CFSG.KD.TPM qnF qn 192
#kc_select CFSG.KD.TPM selF sel 192
#kc_select CFSG.KD.TPM xselF xsel 192
#kc_select CFSG.KD.TPM wnF wn 192
#kc_select CFSG.KD.TPM pswF psw 192
#kc_select CFSG.KD.TPM sgXF sgX 192
#kc_select CFSG.KD.TPM sgWF sgW 192
#kc_select CFSG.KD.TPM sgAF sgA 192
#kc_listOf CFSG.KD.TPM keys key 192

namespace CFSG.KD.TPM

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.TPM

end
