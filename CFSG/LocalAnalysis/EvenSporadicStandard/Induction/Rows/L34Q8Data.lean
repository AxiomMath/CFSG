module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.EvenSporadicStandard.L34Q8

open CFSG.PSL3Four.Native

@[expose] def letterTabs : Array Tab :=
  #[g₁T, g₂T, g₃T, invTab 42 g₁T, invTab 42 g₂T, invTab 42 g₃T]

@[expose] def wordT (w : List Nat) : Tab :=
  w.foldr (fun j acc => comp 42 letterTabs[j]! acc) (idTab 42)

@[expose] def wX1 : List Nat := [0, 1, 3, 1, 0, 1, 0, 1, 3, 1]

@[expose] def wY1 : List Nat := [0, 2, 0, 2, 3, 2, 3, 1, 3, 2, 0, 1]

@[expose] def wX4 : List Nat := [1, 3, 2, 3, 2, 0, 1, 0, 1]

@[expose] def wY4 : List Nat := [1, 0, 2, 0, 2, 3, 1, 3, 1]

@[expose] def inverseLettersOK : Bool :=
  allBelow 3 fun j =>
    (letterTabs[j + 3]!).size == 42 &&
      comp 42 letterTabs[j + 3]! letterTabs[j]! == idTab 42

@[expose] def class1OK : Bool :=
  let x := wordT wX1
  let y := wordT wY1
  comp 42 x x == r₁T && comp 42 y y == r₁T && !(r₁T == idTab 42) &&
    comp 42 (comp 42 x y) x == y

@[expose] def class4OK : Bool :=
  let x := wordT wX4
  let y := wordT wY4
  comp 42 x x == comp 42 y y && !(comp 42 x x == idTab 42) && comp 42 (comp 42 x y) x == y &&
    comp 42 x r₄T == comp 42 r₄T x && comp 42 y r₄T == comp 42 r₄T y

@[expose] def q8OK : Bool :=
  letterTabs.size == 6 && inverseLettersOK && class1OK && class4OK

end CFSG.EvenSporadicStandard.L34Q8
