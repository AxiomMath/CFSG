module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7Mono0
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7Mono1
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7Mono2
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.SLP.Gen7M cnF cn 626
#kc_select CFSG.KD.SLP.Gen7M onF on 626
#kc_select CFSG.KD.SLP.Gen7M qnF qn 626
#kc_select CFSG.KD.SLP.Gen7M selF sel 626
#kc_select CFSG.KD.SLP.Gen7M xselF xsel 626
#kc_select CFSG.KD.SLP.Gen7M wnF wn 626
#kc_select CFSG.KD.SLP.Gen7M pswF psw 626
#kc_select CFSG.KD.SLP.Gen7M sgXF sgX 626
#kc_select CFSG.KD.SLP.Gen7M sgWF sgW 626
#kc_select CFSG.KD.SLP.Gen7M sgAF sgA 626
#kc_listOf CFSG.KD.SLP.Gen7M keys key 626
#kc_listDispatch CFSG.KD.SLP.Gen7M keyF key 626

namespace CFSG.KD.SLP.Gen7M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.SLP.Gen7M

namespace CFSG.KD.SLP.Gen7ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.SLP.Gen7M.keyF k) (CFSG.KD.SLP.Gen7M.ents k)

end CFSG.KD.SLP.Gen7ME

end
