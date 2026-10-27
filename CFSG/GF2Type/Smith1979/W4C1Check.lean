module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCertInputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C1

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U

@[expose] def g0C : List ℕ :=
  [1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def g0I : List ℕ :=
  [1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def g1C : List ℕ :=
  [1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1]

@[expose] def g1I : List ℕ :=
  [1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1]

@[expose] def g2C : List ℕ :=
  [1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1]

@[expose] def g2I : List ℕ :=
  [1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1]

@[expose] def g3C : List ℕ :=
  [1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1]

@[expose] def g3I : List ℕ :=
  [1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1]

@[expose] def g4C : List ℕ :=
  [1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1]

@[expose] def g4I : List ℕ :=
  [1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1]

@[expose] def w2C : List ℕ :=
  [1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def syP : List (List ℕ × List ℕ) :=
  [(g0C, g0I), (g1C, g1I), (g2C, g2I), (g3C, g3I), (g4C, g4I)]

@[expose] def syG : List (List ℕ) :=
  syP.map Prod.fst

abbrev syT : Array (List ℕ) :=
  closureT syG

@[expose] def centralInv (z : List ℕ) : Bool :=
  mul6 z z == one6 && !(z == one6) && syG.all fun s => mul6 s z == mul6 z s

@[expose] def condX (z x : List ℕ) : Bool :=
  mul6 x x == one6 && !(x == one6) && !(x == z) && mul6 x z == mul6 z x &&
    syG.all fun s => mul6 s x == mul6 x s || mul6 s x == mul6 (mul6 x z) s

@[expose] def condY (z x y : List ℕ) : Bool :=
  mul6 y y == one6 && !(y == one6) && !(y == z) && !(y == x) && !(y == mul6 x z) &&
    mul6 y z == mul6 z y && mul6 y x == mul6 x y &&
    syG.all fun s => mul6 s y == mul6 y s || mul6 s y == mul6 (mul6 y z) s ||
      mul6 s y == mul6 (mul6 y x) s || mul6 s y == mul6 (mul6 y (mul6 x z)) s

@[expose] def inT8 (z x y w : List ℕ) : Bool :=
  w == one6 || w == z || w == x || w == mul6 x z || w == y || w == mul6 y z ||
    w == mul6 y x || w == mul6 y (mul6 x z)

@[expose] def chainOK : Bool :=
  syT.toList.all fun z => !centralInv z ||
    syT.toList.all fun x => !condX z x ||
      syT.toList.all fun y => !condY z x y || inT8 z x y w2C

@[expose] def chk : Bool :=
  syP.all pairCheck && closureOK syG syT 512 && syT.contains w2C && !(w2C == one6) && chainOK

end CFSG.GF2Type.Smith1979.W4C1
