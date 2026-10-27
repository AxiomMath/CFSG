module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Fix.Data.W2
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F

@[expose] def w2s (s : Nat) : Bool :=
  chainOK QWs2 (eBase (CFSG.KD.Fi22KM.WJs 2) 220) (8 * s) (Nat.min 8 (220 - 8 * s))

@[expose] def h2s (s : Nat) : Bool :=
  chainOK QWs2 (hBase (CFSG.KC.Fi22B.sub 2) 220) (220 + 8 * s) (Nat.min 8 (9 - 8 * s))

theorem wI2 : idOK (QWs2 0) = true := by quickRfl

theorem wF2 : idOK (QWs2 229) = true := by quickRfl

end CFSG.KD.Fi22F

#kc_each_unfold CFSG.KD.Fi22F.w2s 0 28
#kc_each_unfold CFSG.KD.Fi22F.h2s 0 2

end
