module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Fix.Data.W3
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F

@[expose] def w3s (s : Nat) : Bool :=
  chainOK QWs3 (eBase (CFSG.KD.Fi22KM.WJs 3) 130) (8 * s) (Nat.min 8 (130 - 8 * s))

@[expose] def h3s (s : Nat) : Bool :=
  chainOK QWs3 (hBase (CFSG.KC.Fi22B.sub 3) 130) (130 + 8 * s) (Nat.min 8 (5 - 8 * s))

theorem wI3 : idOK (QWs3 0) = true := by quickRfl

theorem wF3 : idOK (QWs3 135) = true := by quickRfl

end CFSG.KD.Fi22F

#kc_each_unfold CFSG.KD.Fi22F.w3s 0 17
#kc_each_unfold CFSG.KD.Fi22F.h3s 0 1

end
