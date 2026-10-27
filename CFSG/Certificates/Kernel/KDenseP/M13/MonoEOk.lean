module

public import CFSG.Certificates.Kernel.KDenseP.M13.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.M13M keyF key 76

namespace CFSG.KD.M13ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.M13M.keyF k) (CFSG.KD.M13M.ents k)

end CFSG.KD.M13ME

end
