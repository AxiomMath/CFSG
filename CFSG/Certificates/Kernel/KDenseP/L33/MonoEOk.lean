module

public import CFSG.Certificates.Kernel.KDenseP.L33.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.L33M keyF key 19

namespace CFSG.KD.L33ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.L33M.keyF k) (CFSG.KD.L33M.ents k)

end CFSG.KD.L33ME

end
