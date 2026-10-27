module

public import CFSG.Certificates.Kernel.KDenseP.CM12.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.CM12M keyF key 22

namespace CFSG.KD.CM12ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.CM12M.keyF k) (CFSG.KD.CM12M.ents k)

end CFSG.KD.CM12ME

end
