
module

public import CFSG.Sporadic.Schreier.J4SOddData
public import CFSG.Sporadic.Schreier.J4SKCentBase

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

@[expose] def h11Poly (w : ℕ) : Array ℕ :=
  Array.ofFn (n := 11) fun i => app11 (powCols (wordCols a276Word) i) w

@[expose] def h11B : Array ℕ := #[1, 76, 746, 1657, 1579, 848, 778, 1591, 1843, 290, 647]

@[expose] def h11Binv : Array ℕ := #[1, 138, 1805, 120, 2021, 1031, 1911, 1465, 1677, 1599, 731]

@[expose] def h11X (w : ℕ) : Array ℕ := comp11 (h11Poly w) h11Binv

end CFSG.Sporadic.J4Schreier
