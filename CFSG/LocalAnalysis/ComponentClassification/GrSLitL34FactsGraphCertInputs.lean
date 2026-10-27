module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2CertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def cbit (κ k w : ℕ) : Bool := commBit κ k w true

@[expose] def bitsOK : Bool :=
  [0, 1, 2].all fun κ => (List.range 16).all fun k => [4, 8].all fun w =>
    commBit κ k w (cbit κ k w) && commBit κ (4 * k) w (cbit κ (4 * k) w)

@[expose] def xTab (k m : ℕ) : Tab := comp 42 (wordTab (tg k)) (wordTab (tg (4 * m)))

@[expose] def decompOK : Bool :=
  allBelow 64 fun k => anyBelow 16 fun k₁ => anyBelow 16 fun m => xTab k₁ m == wordTab (tg k)

@[expose] def xc (κ k m : ℕ) : Bool :=
  (cbit κ k 4 == cbit κ (4 * m) 4) && (cbit κ k 8 == cbit κ (4 * m) 8)

@[expose] def xTabs (κ : ℕ) : List Tab :=
  (List.range 16).flatMap fun k => ((List.range 16).filter (xc κ k)).map (xTab k)

@[expose] def xAll : List (List Tab) := [xTabs 0, xTabs 1, xTabs 2]

@[expose] def invertOK (X : List (List Tab)) (ρ : Tab) : Bool :=
  !(comp 42 ρ (wordTab (tg 4)) == comp 42 (wordTab (tg 4)) ρ &&
      comp 42 ρ (wordTab (tg 8)) == comp 42 (wordTab (tg 8)) ρ) ||
    X.all fun L => L.all fun x => !(L.contains (conjTab 42 ρ ρ x)) ||
      comp 42 (conjTab 42 ρ ρ x) x == idTab 42

@[noinline, expose] def graphOK : Bool :=
  bitsOK && decompOK && [r₂T, r₃T, r₄T].all fun ρ =>
    (orbitBFS 42 gTabs (gTabs.map (invTab 42)) ρ 1963).tabs.toList.all (invertOK xAll)

end CFSG.ComponentClassification.GrSLit.L34Facts
