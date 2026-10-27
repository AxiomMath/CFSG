module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Fix.Data.W0
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F

@[expose] def w0s (s : Nat) : Bool :=
  chainOK QWs0 (eBase (CFSG.KD.Fi22KM.WJs 0) 431) (8 * s) (Nat.min 8 (431 - 8 * s))

@[expose] def h0s (s : Nat) : Bool :=
  chainOK QWs0 (hBase (CFSG.KC.Fi22B.sub 0) 431) (431 + 8 * s) (Nat.min 8 (1 - 8 * s))

theorem wI0 : idOK (QWs0 0) = true := by quickRfl

theorem wF0 : idOK (QWs0 432) = true := by quickRfl

end CFSG.KD.Fi22F

#kc_each_unfold CFSG.KD.Fi22F.w0s 0 54
#kc_each_unfold CFSG.KD.Fi22F.h0s 0 1

end
