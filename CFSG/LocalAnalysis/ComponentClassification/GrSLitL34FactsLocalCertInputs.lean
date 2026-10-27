module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def tgT (k : ℕ) : Tab := wordTab (tg k)

@[expose] def quatOK : Bool :=
  comp 42 (tgT 35) (tgT 35) == tgT 4 && comp 42 (tgT 38) (tgT 38) == tgT 4 &&
    comp 42 (tgT 4) (tgT 4) == idTab 42 && !(tgT 4 == idTab 42) &&
    comp 42 (tgT 35) (tgT 38) == comp 42 (comp 42 (tgT 38) (tgT 4)) (tgT 35) &&
    !(tgT 38 == idTab 42) && !(tgT 38 == tgT 35) && !(tgT 38 == tgT 4) &&
    !(tgT 38 == comp 42 (tgT 4) (tgT 35))

@[expose] def sylWit : List (ℕ × List ℕ) :=
  [(0, []),
    (1, [0]),
    (4, [0, 0]),
    (11, [2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 2]),
    (23, [1, 0, 2, 0, 1, 0, 0, 2, 1, 0, 0, 1]),
    (24, [1, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1]),
    (43, [1, 0, 2, 0, 2, 0, 0, 1, 0, 0, 1]),
    (44, [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1]),
    (74, [1, 0, 0, 1, 0, 0, 2, 0, 2, 0, 1])]

@[expose] def invOK (x : Tab) : Bool :=
  (invTab 42 x).size == 42 && comp 42 (invTab 42 x) x == idTab 42

@[expose] def r4Conj (y : Tab) : Tab := conjTab 42 (invTab 42 y) y r₄T

@[expose] def r4NotNormalizes (y : Tab) : Bool :=
  let ET := enumBFS 42 (wordTabs wT₀) 64
  anyBelow (wordTabs wT₀).size fun i =>
    notInOK ET.tabs (conjTab 42 (r4Conj y) (r4Conj y) (wordTabs wT₀)[i]!)

@[expose] def sylWitOK : Bool :=
  let EB := enumBFS 42 (wordTabs wB₀) 192
  allBelow wReps.length fun k =>
    r4NotNormalizes (wordTab (wReps.getD k [])) ||
      sylWit.any fun e => e.1 == k &&
        comp 42 (wordTab e.2) r₄T == comp 42 r₄T (wordTab e.2) &&
        invOK (wordTab e.2) &&
        found (indexOf EB.tabs) EB.tabs
          (comp 42 (invTab 42 (wordTab e.2)) (wordTab (wReps.getD k [])))

@[noinline, expose] def localOK : Bool :=
  quatOK && sylWitOK

end CFSG.ComponentClassification.GrSLit.L34Facts
