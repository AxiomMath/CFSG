module

public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoTab
public import Certificates.Data.Kernel.KDenseP.Words
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain

public section

namespace CFSG.KD.AX

open CFSG.KC.KDense

@[expose] noncomputable def run3 (w : List Nat) (c : Nat) (s : St) : St :=
  CFSG.KC.KDenseP.runN (nat_lit 3) (nat_lit 2) CFSG.KD.KDF.F CFSG.KD.AXM.MT
    (CFSG.KC.KDenseP.decW w) (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

@[expose] noncomputable def run7 (w : List Nat) (c : Nat) (s : St) : St :=
  CFSG.KC.KDenseP.runN (nat_lit 7) (nat_lit 3) CFSG.KD.KDF.F CFSG.KD.AXM.MT
    (CFSG.KC.KDenseP.decW w) (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

end CFSG.KD.AX

end
