module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Fix.Data.W5
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F

@[expose] def w5s (s : Nat) : Bool :=
  chainOK QWs5 (eBase (CFSG.KD.Fi22KM.WJs 5) 216) (8 * s) (Nat.min 8 (216 - 8 * s))

@[expose] def h5s (s : Nat) : Bool :=
  chainOK QWs5 (hBase (CFSG.KC.Fi22B.sub 5) 216) (216 + 8 * s) (Nat.min 8 (11 - 8 * s))

theorem wI5 : idOK (QWs5 0) = true := by quickRfl

theorem wF5 : idOK (QWs5 227) = true := by quickRfl

end CFSG.KD.Fi22F

#kc_each_unfold CFSG.KD.Fi22F.w5s 0 27
#kc_each_unfold CFSG.KD.Fi22F.h5s 0 2

end
