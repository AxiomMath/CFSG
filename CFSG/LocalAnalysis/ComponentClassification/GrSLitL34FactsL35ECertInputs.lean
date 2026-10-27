module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

@[expose] def fieldZSpecs : List (List (Fin 2 × Bool) × ℕ × ℕ × ℕ) :=
  [(alphaF zOne, 1, 0, 0), (alphaF zTwo, 3, 3, 0)]

@[expose] def r3Idx : List ℕ := [4, 8]

end CFSG.ComponentClassification.GrSLit.L34Facts
