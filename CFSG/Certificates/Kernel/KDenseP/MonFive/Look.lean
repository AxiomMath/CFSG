module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Run
public import Certificates.Data.Kernel.KDenseP.Look
public import CFSG.Certificates.Kernel.Common.Chain
public import CFSG.Certificates.Kernel.KDenseP.MonFive.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.AgreeTasks
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

#kc_chain CFSG.KD.M5RL "look.plan.txt" 99338 18047022216046423517

namespace CFSG.KD.M5RL

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def look (l : List Nat) : Bool × Nat :=
  lookT CT SC PI (nat_lit 1488) CFSG.KD.M5RM.MT.keys l

@[expose] noncomputable def runRL (p : List (List CFSG.Monster.AxisCount.Native.Gen ×
    List CFSG.Monster.AxisCount.Native.Gen)) (σ c : Nat) (s : St) : St :=
  runNL (nat_lit 4) (nat_lit 2) CFSG.KD.KDF.F CFSG.KD.M5RM.MT look
    (CFSG.KC.KDense.Y443.words p σ) (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

@[expose] noncomputable def chkRL (p : List (List CFSG.Monster.AxisCount.Native.Gen ×
    List CFSG.Monster.AxisCount.Native.Gen)) (S : Nat → St) (c : Nat) : Bool :=
  chunkOKNL (nat_lit 4) (nat_lit 2) (nat_lit 5) CFSG.KD.KDF.F CFSG.KD.M5RM.MT look
    (CFSG.KC.KDense.Y443.words p) S c

end CFSG.KD.M5RL

end
