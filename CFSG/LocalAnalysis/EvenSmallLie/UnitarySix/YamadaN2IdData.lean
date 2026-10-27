module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def commBlk (j : ℕ) (X : Array ℕ) : Array ℕ :=
  bxor 8 (bmul 8 8 (bmul 8 8 (n0Bits2 j) X) (n1Bits2 j)) X

@[expose] def commDecCheck : Bool :=
  (List.range 2).all fun z =>
    candBlock z 1 == commBlk 3 (candBlock z 2) &&
    candBlock z 0 == bxor 8 (commBlk 3 (candBlock z 2)) (commBlk 3 (candBlock z 3)) &&
    candBlock z 3 == commBlk 1 (candBlock z 0) &&
    candBlock z 2 == bxor 8 (commBlk 1 (candBlock z 0)) (commBlk 1 (candBlock z 1))

@[expose] def pmBits : Array ℕ :=
  Array.ofFn (n := 18) fun r =>
    if (r : ℕ) < 9 then 2 ^ ((r : ℕ) + 9) else 2 ^ ((r : ℕ) - 9) + 2 ^ (r : ℕ)

@[expose] def pmiBits : Array ℕ :=
  Array.ofFn (n := 18) fun r =>
    if (r : ℕ) < 9 then 2 ^ (r : ℕ) + 2 ^ ((r : ℕ) + 9) else 2 ^ ((r : ℕ) - 9)

@[expose] def uIdCheck : Bool :=
  bmul 18 18 pmBits pmiBits == id18 && bmul 18 18 pmiBits pmBits == id18 &&
  (List.range 4).all fun m =>
    candXBits 0 m ==
      bmul 18 18 (bmul 18 18 pmBits (bd9Bits (genABits (Fin.ofNat 12 m)) id9)) pmiBits

@[expose] def kBits (A B : Fin 3 → Fin 3 → ℕ) : Array ℕ :=
  bmul 18 18 (bmul 18 18 pciBits (reBits9 (krCode A B))) pcBits

@[expose] def idCode (i j : Fin 3) : ℕ := if i = j then 1 else 0

@[expose] def lTr (m : ℕ) : Fin 3 × Fin 3 × ℕ :=
  if m = 0 then (1, 0, 1) else if m = 1 then (1, 0, 3) else if m = 2 then (2, 0, 1) else (2, 0, 3)

@[expose] def lGen (m : ℕ) : Array ℕ :=
  if m = 0 then genABits 1 else if m = 1 then bmul 9 9 (genABits 0) (genABits 1)
  else if m = 2 then genABits 3 else bmul 9 9 (genABits 2) (genABits 3)

@[expose] def lIdCheck : Bool :=
  (List.range 4).all fun m =>
    candXBits 1 m == bmul 18 18 (kBits idCode (trCode3 (lTr m).2.1 (lTr m).1 (lTr m).2.2))
      (bd9Bits (lGen m) (lGen m))

@[expose] def tlCheck : Bool :=
  (List.finRange 12).all fun s =>
    bmul 18 18 tauBits (bmul 18 18 (kBits (trCode3 (pairOf s).1 (pairOf s).2 (coefCode s)) idCode)
      tauBits) ==
      kBits idCode (trCode3 (pairOf s).1 (pairOf s).2 (frobCode (coefCode s)))

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
