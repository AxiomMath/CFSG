module

public import CFSG.Certificates.Kernel.KDenseP.MonSeven.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.M7M keyF key 638

namespace CFSG.KD.M7ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.M7M.keyF k) (CFSG.KD.M7M.ents k)

end CFSG.KD.M7ME

end
