module

public import CFSG.Certificates.Kernel.KDenseP.E11.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.E11M keyF key 32

namespace CFSG.KD.E11ME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.E11M.keyF k) (CFSG.KD.E11M.ents k)

end CFSG.KD.E11ME

end
