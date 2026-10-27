module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Mono0
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Mono1
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.SLP.Gen13M cnF cn 501
#kc_select CFSG.KD.SLP.Gen13M onF on 501
#kc_select CFSG.KD.SLP.Gen13M qnF qn 501
#kc_select CFSG.KD.SLP.Gen13M selF sel 501
#kc_select CFSG.KD.SLP.Gen13M xselF xsel 501
#kc_select CFSG.KD.SLP.Gen13M wnF wn 501
#kc_select CFSG.KD.SLP.Gen13M pswF psw 501
#kc_select CFSG.KD.SLP.Gen13M sgXF sgX 501
#kc_select CFSG.KD.SLP.Gen13M sgWF sgW 501
#kc_select CFSG.KD.SLP.Gen13M sgAF sgA 501
#kc_listOf CFSG.KD.SLP.Gen13M keys key 501
#kc_listDispatch CFSG.KD.SLP.Gen13M keyF key 501

namespace CFSG.KD.SLP.Gen13M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.SLP.Gen13M

namespace CFSG.KD.SLP.Gen13ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.SLP.Gen13M.keyF k) (CFSG.KD.SLP.Gen13M.ents k)

end CFSG.KD.SLP.Gen13ME

end
