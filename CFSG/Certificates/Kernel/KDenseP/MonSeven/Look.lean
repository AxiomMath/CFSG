module

public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Run
public import Certificates.Data.Kernel.KDenseP.Look
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Chain
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

#kc_chain CFSG.KD.M7L "look.plan.txt" 42600 8639487697920514786

namespace CFSG.KD.M7L

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def look (l : List Nat) : Bool × Nat :=
  lookT CT SC PI (nat_lit 638) CFSG.KD.M7M.MT.keys l

@[expose] noncomputable def chkPL (P : CFSG.KC.KDenseP.MonSeven.Prs) (S : Nat → St) (c : Nat) :
    Bool :=
  chunkOKNL (nat_lit 4) (nat_lit 2) (nat_lit 5) CFSG.KD.KDF.F CFSG.KD.M7M.MT look
    (CFSG.KC.KDense.Y443.words P) S c

@[expose] noncomputable def runCP (P : CFSG.KC.KDenseP.MonSeven.Prs) (c : Nat) (s : St) : St :=
  runNL (nat_lit 4) (nat_lit 2) CFSG.KD.KDF.F CFSG.KD.M7M.MT look
    (CFSG.KC.KDense.Y443.words P (f20 c (nat_lit 0))) (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

@[expose] noncomputable def grpRP (P : CFSG.KC.KDenseP.MonSeven.Prs) (CH PR : Nat → Nat)
    (G : Nat → List Nat) (g : Nat) : Bool :=
  grpL (runCP P) (chkPL P) CH PR G CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M7L

end
