module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def witF : List (Fin 2 × Bool) := tw 28

@[expose] def witG : List (Fin 2 × Bool) := tw 8 ++ zOne

@[expose] def witU : List (Fin 2 × Bool) := tw 4 ++ zOne ++ zTwo

@[expose] def witSpecs : List (List (Fin 2 × Bool) × ℕ × ℕ × ℕ) :=
  [(FreeGroup.invRev witF ++ alphaF witF, 0, 0, 2), (wpow witF 2, 0, 0, 1),
    (FreeGroup.invRev witG ++ alphaG witG, 0, 0, 0), (wpow witG 2, 0, 0, 0),
    (FreeGroup.invRev witU ++ alphaU witU, 0, 0, 0), (wpow witU 2, 0, 0, 1)]

@[expose] def syl3Wit : List (ℕ × List ℕ) :=
  [(0, []), (1, [0]), (4, [0, 0]), (98, [1, 0, 1, 0, 2, 0, 0, 1, 0, 2, 0, 1]),
    (101, [1, 0, 2, 0, 2, 0, 0, 2, 0, 2, 0, 1])]

@[expose] def invOK3 (x : Tab) : Bool :=
  (invTab 42 x).size == 42 && comp 42 (invTab 42 x) x == idTab 42

@[expose] def r3Conj (y : Tab) : Tab := conjTab 42 (invTab 42 y) y r₃T

@[expose] def r3NotNormalizes (y : Tab) : Bool :=
  let ET := enumBFS 42 (wordTabs wT₀) 64
  anyBelow (wordTabs wT₀).size fun i =>
    notInOK ET.tabs (conjTab 42 (r3Conj y) (r3Conj y) (wordTabs wT₀)[i]!)

@[expose] def syl3WitOK : Bool :=
  let EB := enumBFS 42 (wordTabs wB₀) 192
  allBelow wReps.length fun k =>
    r3NotNormalizes (wordTab (wReps.getD k [])) ||
      syl3Wit.any fun e => e.1 == k &&
        comp 42 (wordTab e.2) r₃T == comp 42 r₃T (wordTab e.2) &&
        invOK3 (wordTab e.2) &&
        found (indexOf EB.tabs) EB.tabs
          (comp 42 (invTab 42 (wordTab e.2)) (wordTab (wReps.getD k [])))

end CFSG.ComponentClassification.GrSLit.GrS4
