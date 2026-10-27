module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs

public section

namespace CFSG.OddStandard.ONanRec.IdCert

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def tgT (k : ℕ) : Tab := wordTab (tg k)

@[expose] def comT (x y : Tab) : Bool := comp 42 x y == comp 42 y x

@[expose] def q8PairT (ρ : Tab) (m₁ m₂ : ℕ) : Bool :=
  comT (tgT m₁) ρ && comT (tgT m₂) ρ && !(comp 42 (tgT m₁) (tgT m₁) == idTab 42) &&
    (comp 42 (tgT m₁) (tgT m₁) == comp 42 (tgT m₂) (tgT m₂)) && !(comT (tgT m₁) (tgT m₂))

@[expose] def sigmaCase (ρ : Tab) : Bool :=
  !(comp 42 ρ ρ == idTab 42) ||
    !((List.range 64).any fun m₁ => (List.range 64).any fun m₂ => q8PairT ρ m₁ m₂) ||
    (List.range 64).any fun m => comp 42 (tgT m) ρ == comp 42 r₄T (tgT m)

@[expose] def sigmaOK : Bool :=
  (List.range 64).all fun k => [r₂T, r₃T, r₄T].all fun v => sigmaCase (comp 42 (tgT k) v)

@[expose] def aOne : List ℕ := [0, 4, 8, 12, 18, 21, 27, 30, 35, 37, 41, 47, 50, 55, 57, 62]

@[expose] def aTwo : List ℕ := [0, 4, 8, 12, 19, 22, 25, 31, 33, 38, 42, 45, 51, 53, 58, 63]

@[expose] def aThree : List ℕ := [0, 4, 8, 12, 17, 23, 26, 29, 34, 39, 43, 46, 49, 54, 59, 61]

@[expose] def aCent : List (ℕ × List ℕ) :=
  [(35, aOne), (47, aOne), (38, aTwo), (58, aTwo), (49, aThree), (61, aThree)]

@[expose] def centOK : Bool :=
  aCent.all fun d => (List.range 64).all fun m => comT (tgT m) (tgT d.1) == d.2.contains m

@[expose] def idCommData : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(35, 18, 2, 1, 0), (38, 19, 1, 3, 0), (49, 23, 3, 2, 0)]

@[expose] def idSpecs : List (List (Fin 2 × Bool) × ℕ × ℕ × ℕ) :=
  idCommData.map fun d => (commWord (tw d.1) (tw d.2.1), d.2.2.1, d.2.2.2.1, d.2.2.2.2)

end CFSG.OddStandard.ONanRec.IdCert
