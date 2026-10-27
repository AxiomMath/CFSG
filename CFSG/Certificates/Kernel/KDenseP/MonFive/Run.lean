module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.MonoTab
public import Certificates.Data.Kernel.KDenseP.Chunk
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs

public section

namespace CFSG.KD.M5R

open CFSG.KC.KDense

@[expose] noncomputable def runR (p : List (List CFSG.Monster.AxisCount.Native.Gen ×
    List CFSG.Monster.AxisCount.Native.Gen)) (σ c : Nat) (s : St) : St :=
  CFSG.KC.KDenseP.runN (nat_lit 4) (nat_lit 2) CFSG.KD.KDF.F CFSG.KD.M5RM.MT
    (CFSG.KC.KDense.Y443.words p σ) (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

@[expose] noncomputable def chkR (p : List (List CFSG.Monster.AxisCount.Native.Gen ×
    List CFSG.Monster.AxisCount.Native.Gen)) (S : Nat → St) (c : Nat) : Bool :=
  CFSG.KC.KDenseP.chunkOKN (nat_lit 4) (nat_lit 2) (nat_lit 5) CFSG.KD.KDF.F CFSG.KD.M5RM.MT
    (CFSG.KC.KDense.Y443.words p) S c

end CFSG.KD.M5R

end
