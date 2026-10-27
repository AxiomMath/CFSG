module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Fix.Data.E
public import CFSG.Certificates.Kernel.Fi22.Bound2.Rels
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F

@[expose] def e0s (s : Nat) : Bool :=
  chainOK QEs0 (hBase (CFSG.KC.Fi22K.subY 7) 0) (8 * s) (Nat.min 8 (31 - 8 * s))

@[expose] def e1s (s : Nat) : Bool :=
  chainOK QEs1 (hBase (CFSG.KC.Fi22K.subY 8) 0) (8 * s) (Nat.min 8 (29 - 8 * s))

@[expose] def e2s (s : Nat) : Bool :=
  chainOK QEs2 (hBase (CFSG.KC.Fi22K.subY 9) 0) (8 * s) (Nat.min 8 (27 - 8 * s))

@[expose] def e3s (s : Nat) : Bool :=
  chainOK QEs3 (hBase (CFSG.KC.Fi22K.subY 10) 0) (8 * s) (Nat.min 8 (25 - 8 * s))

@[expose] def e4s (s : Nat) : Bool :=
  chainOK QEs4 (hBase (CFSG.KC.Fi22K.subY 11) 0) (8 * s) (Nat.min 8 (25 - 8 * s))

@[expose] def e5s (s : Nat) : Bool :=
  chainOK QEs5 (hBase (CFSG.KC.Fi22K.subY 12) 0) (8 * s) (Nat.min 8 (29 - 8 * s))

theorem eI0 : idOK (QEs0 0) = true := by quickRfl
theorem eE0 : Nat.beq (QEs0 31) E0 = true := by quickRfl
theorem eI1 : idOK (QEs1 0) = true := by quickRfl
theorem eE1 : Nat.beq (QEs1 29) E1 = true := by quickRfl
theorem eI2 : idOK (QEs2 0) = true := by quickRfl
theorem eE2 : Nat.beq (QEs2 27) E2 = true := by quickRfl
theorem eI3 : idOK (QEs3 0) = true := by quickRfl
theorem eE3 : Nat.beq (QEs3 25) E3 = true := by quickRfl
theorem eI4 : idOK (QEs4 0) = true := by quickRfl
theorem eE4 : Nat.beq (QEs4 25) E4 = true := by quickRfl
theorem eI5 : idOK (QEs5 0) = true := by quickRfl
theorem eE5 : Nat.beq (QEs5 29) E5 = true := by quickRfl

end CFSG.KD.Fi22F

#kc_each_unfold CFSG.KD.Fi22F.e0s 0 4
#kc_each_unfold CFSG.KD.Fi22F.e1s 0 4
#kc_each_unfold CFSG.KD.Fi22F.e2s 0 4
#kc_each_unfold CFSG.KD.Fi22F.e3s 0 4
#kc_each_unfold CFSG.KD.Fi22F.e4s 0 4
#kc_each_unfold CFSG.KD.Fi22F.e5s 0 4

end
