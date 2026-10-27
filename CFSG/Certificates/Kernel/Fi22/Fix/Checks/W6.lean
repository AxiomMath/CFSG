module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Fix.Data.W6
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F

@[expose] def w6s (s : Nat) : Bool :=
  chainOK QWs6 (eBase (CFSG.KD.Fi22KM.WJs 6) 173) (8 * s) (Nat.min 8 (173 - 8 * s))

@[expose] def h6s (s : Nat) : Bool :=
  chainOK QWs6 (hBase (CFSG.KC.Fi22B.sub 6) 173) (173 + 8 * s) (Nat.min 8 (17 - 8 * s))

theorem wI6 : idOK (QWs6 0) = true := by quickRfl

theorem wF6 : idOK (QWs6 190) = true := by quickRfl

end CFSG.KD.Fi22F

#kc_each_unfold CFSG.KD.Fi22F.w6s 0 22
#kc_each_unfold CFSG.KD.Fi22F.h6s 0 3

end
