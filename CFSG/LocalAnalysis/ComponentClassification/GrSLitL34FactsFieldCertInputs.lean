module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def syl2Wit : List (ℕ × List ℕ) :=
    [(0, []), (1, [0]), (2, [1]), (4, [0, 0]), (5, [1, 0]), (7, [0, 1]), (10, [1, 0, 0]),
     (12, [0, 1, 0]), (15, [0, 0, 1]), (16, [1, 0, 1]), (22, [0, 1, 0, 0]), (25, [1, 0, 1, 0]),
     (31, [1, 0, 0, 1]), (42, [0, 0, 1, 0, 0]), (47, [0, 1, 0, 1, 0]), (58, [0, 1, 0, 0, 1]),
     (79, [0, 0, 1, 0, 1, 0]), (80, [1, 0, 1, 0, 1, 0]), (90, [0, 0, 1, 0, 0, 1]),
     (100, [0, 1, 0, 1, 0, 1, 0]), (103, [1, 0, 0, 1, 0, 0, 1])]

@[expose] def r2Conj (y : Tab) : Tab := conjTab 42 (invTab 42 y) y r₂T

@[expose] def r2NotNormalizes (y : Tab) : Bool :=
  let ET := enumBFS 42 (wordTabs wT₀) 64
  anyBelow (wordTabs wT₀).size fun i =>
    notInOK ET.tabs (conjTab 42 (r2Conj y) (r2Conj y) (wordTabs wT₀)[i]!)

@[expose] def syl2WitOK : Bool :=
  let EB := enumBFS 42 (wordTabs wB₀) 192
  allBelow wReps.length fun k =>
    r2NotNormalizes (wordTab (wReps.getD k [])) ||
      syl2Wit.any fun e => e.1 == k &&
        comp 42 (wordTab e.2) r₂T == comp 42 r₂T (wordTab e.2) &&
        invOK (wordTab e.2) &&
        found (indexOf EB.tabs) EB.tabs
          (comp 42 (invTab 42 (wordTab e.2)) (wordTab (wReps.getD k [])))

@[expose] def fieldFreeOK : Bool :=
  allBelow 64 fun k =>
    !(comp 42 (comp 42 (comp 42 r₂T (tgT k)) r₂T) (tgT k) == idTab 42) ||
      anyBelow 64 fun m => invOK (tgT m) && [0, 4, 8, 12].any fun z =>
        tgT k == comp 42 (comp 42 (comp 42 (comp 42 (tgT m) r₂T) (invTab 42 (tgT m))) r₂T)
          (tgT z)

@[noinline, expose] def fieldOK : Bool :=
  syl2WitOK && fieldFreeOK

end CFSG.ComponentClassification.GrSLit.L34Facts
