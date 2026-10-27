module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Tab
public import Certificates.Data.Kernel.KDenseP.Words

public section

namespace CFSG.KD.SLP.GenD13

open CFSG.KC.KDense

@[expose] noncomputable def run (w : List Nat) (c : Nat) (s : St) : St :=
  CFSG.KC.KDenseP.runN (nat_lit 4) (nat_lit 2) CFSG.KD.KDF.F CFSG.KD.SLP.GenD13M.MT
    (CFSG.KC.KDenseP.decW w) (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) s

@[expose] noncomputable def chk (WL : Nat → List CFSG.Monster.AxisCount.Native.Gen) (S : Nat → St)
    (c : Nat) : Bool :=
  CFSG.KC.KDenseP.chunkOKN (nat_lit 4) (nat_lit 2) (nat_lit 5) CFSG.KD.KDF.F CFSG.KD.SLP.GenD13M.MT WL S c

end CFSG.KD.SLP.GenD13

end
