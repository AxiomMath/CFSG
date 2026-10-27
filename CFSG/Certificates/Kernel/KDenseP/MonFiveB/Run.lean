module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.MonoTab
public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Pairs
public import Certificates.Data.Kernel.KDenseP.Chunk
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs

public section

namespace CFSG.KD.M5B

open CFSG.KC.KDense

@[expose] noncomputable def runB (b : List Nat) (σ c : Nat) (s : St) : St :=
  CFSG.KC.KDenseP.runN (nat_lit 4) (nat_lit 2) CFSG.KD.KDF.F CFSG.KD.M5BM.MT
    (CFSG.KC.KDense.Y443.words (CFSG.KC.KDenseP.MonFiveB.tri b) σ) (f20 c (nat_lit 1))
    (f20 c (nat_lit 2)) s

@[expose] noncomputable def chkB (b : List Nat) (S : Nat → St) (c : Nat) : Bool :=
  CFSG.KC.KDenseP.chunkOKN (nat_lit 4) (nat_lit 2) (nat_lit 5) CFSG.KD.KDF.F CFSG.KD.M5BM.MT
    (CFSG.KC.KDense.Y443.words (CFSG.KC.KDenseP.MonFiveB.tri b)) S c

end CFSG.KD.M5B

end
