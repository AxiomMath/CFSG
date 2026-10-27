module

public import CFSG.Sporadic.Th.Max3.AllConj
public import CFSG.Certificates.Kernel.ThDemp.OrbBound
public import Certificates.Certificate10088Base
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.AllConj

@[expose] def bitsOf (n : ℕ) : Fin 8 → ℕ := fun i => n / 2 ^ i.val % 2

@[expose] def rowsA1 : Array V4 := rowsNf 0 (bitsOf 1)

@[expose] def rowsA2 : Array V4 := rowsNf 0 (bitsOf 50)

@[expose] def rowsA3 : Array V4 := rowsNf 0 (bitsOf 100)

@[expose] def rowsAEl (e : ℕ) : Array V4 :=
  mulRows (mulRows (mulRows (powRows rowsZ (e % 2)) (powRows rowsA1 (e / 2 % 2)))
    (powRows rowsA2 (e / 4 % 2))) (powRows rowsA3 (e / 8 % 2))

@[expose] def rowsN1 : Array V4 := mulRows rowsX rowsY

@[expose] def rowsN2 : Array V4 := mulRows (wordRows rowsX rowsY [.y, .x, .y]) rowsFusionQ0

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
