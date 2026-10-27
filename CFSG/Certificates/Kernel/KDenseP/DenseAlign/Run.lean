module

public import CFSG.Certificates.Kernel.KDenseP.DenseAlign.MonoTab
public import CFSG.Certificates.Kernel.KDenseP.HeSeven.Pairs
public import Certificates.Data.Kernel.KDenseP.Chunk
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs

public section

namespace CFSG.KD.DA7

open CFSG.KC.KDense

@[expose] noncomputable def runP (P : CFSG.KC.KDenseP.HeSeven.Prs) (σ c : Nat) (s : St) : St :=
  CFSG.KC.KDenseP.runN (nat_lit 4) (nat_lit 2) CFSG.KD.KDF.F CFSG.KD.DA7M.MT
    (CFSG.KC.KDense.Y443.words P σ) (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

@[expose] noncomputable def chkP (P : CFSG.KC.KDenseP.HeSeven.Prs) (S : Nat → St) (c : Nat) : Bool :=
  CFSG.KC.KDenseP.chunkOKN (nat_lit 4) (nat_lit 2) (nat_lit 5) CFSG.KD.KDF.F CFSG.KD.DA7M.MT
    (CFSG.KC.KDense.Y443.words P) S c

end CFSG.KD.DA7

end
