module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Look
public import Certificates.Data.Kernel.KDenseP.Replay

public section

namespace CFSG.KD.M5RL

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def runCL (p : List (List CFSG.Monster.AxisCount.Native.Gen ×
    List CFSG.Monster.AxisCount.Native.Gen)) (c : Nat) (s : St) : St :=
  runRL p (f20 c (nat_lit 0)) c s

@[expose] noncomputable def grpRL (p : List (List CFSG.Monster.AxisCount.Native.Gen ×
    List CFSG.Monster.AxisCount.Native.Gen)) (CH PR : Nat → Nat) (G : Nat → List Nat) (g : Nat) :
    Bool :=
  grpL (runCL p) (chkRL p) CH PR G CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M5RL

end
