module

public import CFSG.Certificates.Kernel.KDenseP.HeSeven.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.HE7M keyF key 34

namespace CFSG.KD.HE7ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.HE7M.keyF k) (CFSG.KD.HE7M.ents k)

end CFSG.KD.HE7ME

end
