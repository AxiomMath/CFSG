module

public import CFSG.Certificates.Kernel.KDenseP.DenseAlign.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.DA7M keyF key 39

namespace CFSG.KD.DA7ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.DA7M.keyF k) (CFSG.KD.DA7M.ents k)

end CFSG.KD.DA7ME

end
