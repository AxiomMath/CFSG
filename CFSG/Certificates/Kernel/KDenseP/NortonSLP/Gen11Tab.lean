module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Mono0
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Mono1
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Mono2
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.SLP.Gen11M cnF cn 748
#kc_select CFSG.KD.SLP.Gen11M onF on 748
#kc_select CFSG.KD.SLP.Gen11M qnF qn 748
#kc_select CFSG.KD.SLP.Gen11M selF sel 748
#kc_select CFSG.KD.SLP.Gen11M xselF xsel 748
#kc_select CFSG.KD.SLP.Gen11M wnF wn 748
#kc_select CFSG.KD.SLP.Gen11M pswF psw 748
#kc_select CFSG.KD.SLP.Gen11M sgXF sgX 748
#kc_select CFSG.KD.SLP.Gen11M sgWF sgW 748
#kc_select CFSG.KD.SLP.Gen11M sgAF sgA 748
#kc_listOf CFSG.KD.SLP.Gen11M keys key 748
#kc_listDispatch CFSG.KD.SLP.Gen11M keyF key 748

namespace CFSG.KD.SLP.Gen11M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.SLP.Gen11M

namespace CFSG.KD.SLP.Gen11ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.SLP.Gen11M.keyF k) (CFSG.KD.SLP.Gen11M.ents k)

end CFSG.KD.SLP.Gen11ME

end
