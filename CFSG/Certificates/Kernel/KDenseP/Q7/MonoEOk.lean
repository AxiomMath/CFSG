module

public import CFSG.Certificates.Kernel.KDenseP.Q7.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.Q7M keyF key 8

namespace CFSG.KD.Q7ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.Q7M.keyF k) (CFSG.KD.Q7M.ents k)

end CFSG.KD.Q7ME

end
