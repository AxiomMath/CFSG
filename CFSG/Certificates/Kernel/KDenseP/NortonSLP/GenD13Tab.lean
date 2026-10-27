module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Mono0
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Mono1
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Mono2
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Mono3
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.Common.ListOf

public section

#kc_select CFSG.KD.SLP.GenD13M cnF cn 892
#kc_select CFSG.KD.SLP.GenD13M onF on 892
#kc_select CFSG.KD.SLP.GenD13M qnF qn 892
#kc_select CFSG.KD.SLP.GenD13M selF sel 892
#kc_select CFSG.KD.SLP.GenD13M xselF xsel 892
#kc_select CFSG.KD.SLP.GenD13M wnF wn 892
#kc_select CFSG.KD.SLP.GenD13M pswF psw 892
#kc_select CFSG.KD.SLP.GenD13M sgXF sgX 892
#kc_select CFSG.KD.SLP.GenD13M sgWF sgW 892
#kc_select CFSG.KD.SLP.GenD13M sgAF sgA 892
#kc_listOf CFSG.KD.SLP.GenD13M keys key 892
#kc_listDispatch CFSG.KD.SLP.GenD13M keyF key 892

namespace CFSG.KD.SLP.GenD13M

open CFSG.KC.KDenseP

@[expose] noncomputable def ents (k : Nat) : MonoE :=
  ⟨cnF k, onF k, qnF k, selF k, xselF k, wnF k, pswF k, sgXF k, sgWF k, sgAF k⟩

@[expose] noncomputable def MT : MonoTab := ⟨keys, ents⟩

end CFSG.KD.SLP.GenD13M

namespace CFSG.KD.SLP.GenD13ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.SLP.GenD13M.keyF k) (CFSG.KD.SLP.GenD13M.ents k)

end CFSG.KD.SLP.GenD13ME

end
