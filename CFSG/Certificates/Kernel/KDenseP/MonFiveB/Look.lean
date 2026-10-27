module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Run
public import Certificates.Data.Kernel.KDenseP.Look
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Chain
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.AgreeTasks
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

#kc_chain CFSG.KD.M5BL "look.plan.txt" 37460 7230104957458114746

namespace CFSG.KD.M5BL

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def look (l : List Nat) : Bool × Nat :=
  lookT CT SC PI (nat_lit 561) CFSG.KD.M5BM.MT.keys l

@[expose] noncomputable def chkBL (b : List Nat) (S : Nat → St) (c : Nat) : Bool :=
  chunkOKNL (nat_lit 4) (nat_lit 2) (nat_lit 5) CFSG.KD.KDF.F CFSG.KD.M5BM.MT look
    (CFSG.KC.KDense.Y443.words (CFSG.KC.KDenseP.MonFiveB.tri b)) S c

@[expose] noncomputable def runCB (b : List Nat) (c : Nat) (s : St) : St :=
  runNL (nat_lit 4) (nat_lit 2) CFSG.KD.KDF.F CFSG.KD.M5BM.MT look
    (CFSG.KC.KDense.Y443.words (CFSG.KC.KDenseP.MonFiveB.tri b) (f20 c (nat_lit 0)))
    (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

@[expose] noncomputable def grpRB (b : List Nat) (CH PR : Nat → Nat) (G : Nat → List Nat)
    (g : Nat) : Bool :=
  grpL (runCB b) (chkBL b) CH PR G CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M5BL

end
