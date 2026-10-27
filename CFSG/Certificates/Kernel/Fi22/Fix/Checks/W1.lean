module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Fix.Data.W1
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F

@[expose] def w1s (s : Nat) : Bool :=
  chainOK QWs1 (eBase (CFSG.KD.Fi22KM.WJs 1) 102) (8 * s) (Nat.min 8 (102 - 8 * s))

@[expose] def h1s (s : Nat) : Bool :=
  chainOK QWs1 (hBase (CFSG.KC.Fi22B.sub 1) 102) (102 + 8 * s) (Nat.min 8 (9 - 8 * s))

theorem wI1 : idOK (QWs1 0) = true := by quickRfl

theorem wF1 : idOK (QWs1 111) = true := by quickRfl

end CFSG.KD.Fi22F

#kc_each_unfold CFSG.KD.Fi22F.w1s 0 13
#kc_each_unfold CFSG.KD.Fi22F.h1s 0 2

end
