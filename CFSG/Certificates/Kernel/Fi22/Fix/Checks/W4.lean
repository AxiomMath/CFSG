module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Fix.Data.W4
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F

@[expose] def w4s (s : Nat) : Bool :=
  chainOK QWs4 (eBase (CFSG.KD.Fi22KM.WJs 4) 244) (8 * s) (Nat.min 8 (244 - 8 * s))

@[expose] def h4s (s : Nat) : Bool :=
  chainOK QWs4 (hBase (CFSG.KC.Fi22B.sub 4) 244) (244 + 8 * s) (Nat.min 8 (8 - 8 * s))

theorem wI4 : idOK (QWs4 0) = true := by quickRfl

theorem wF4 : idOK (QWs4 252) = true := by quickRfl

end CFSG.KD.Fi22F

#kc_each_unfold CFSG.KD.Fi22F.w4s 0 31
#kc_each_unfold CFSG.KD.Fi22F.h4s 0 1

end
