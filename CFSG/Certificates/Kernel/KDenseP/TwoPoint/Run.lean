module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoTab
public import Certificates.Data.Kernel.KDenseP.Words
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain

public section

namespace CFSG.KD.TP

open CFSG.KC.KDense

@[expose] noncomputable def run (w : List Nat) (c : Nat) (s : St) : St :=
  CFSG.KC.KDenseP.runN (nat_lit 4) (nat_lit 2) CFSG.KD.KDF.F CFSG.KD.TPM.MT
    (CFSG.KC.KDenseP.decW w) (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

end CFSG.KD.TP

end
