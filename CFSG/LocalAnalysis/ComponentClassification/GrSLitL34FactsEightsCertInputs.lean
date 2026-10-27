module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def conjP1Data : List (ℕ × List ℕ) :=
    [(1, [1, 0, 1]), (2, [0, 0, 2, 0, 1, 0, 1, 0, 0, 2, 0, 1, 0, 1]),
     (3, [0, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 0, 2, 0, 1, 0, 1]), (4, []), (5, [0, 0, 1, 0]),
     (6, [0, 0, 2, 0]), (7, [0, 0, 1, 0, 0, 0, 2, 0]), (8, [0, 0, 2, 0, 1, 0, 1, 0, 0, 2, 0]),
     (9, [0, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0]), (10, [0, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 2, 0]),
     (11, [0, 0, 2, 0, 1, 0, 1]), (12, [0, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 0, 2, 0]),
     (13, [0, 0, 2, 0, 1, 0, 1, 1, 0, 1]), (14, [0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 1]),
     (15, [0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2, 0])]

@[expose] def conjP2Data : List (ℕ × List ℕ) :=
    [(1, []), (2, [1, 2, 0, 0, 1, 0, 1, 0, 1, 2]), (3, [2, 0, 0, 1, 0, 1, 0, 2]),
     (4, [1, 0, 0, 1, 0, 1, 0]), (5, [2, 0, 0, 1, 0, 1, 0, 1, 2, 0, 0, 1, 0, 1, 0]),
     (6, [1, 2, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0]), (7, [1]),
     (8, [1, 2, 0, 0, 1, 0, 1, 0, 2]), (9, [2, 0, 0, 1, 0, 1, 0, 1, 2]), (10, [1, 2]),
     (11, [2, 0, 0, 1, 0, 1, 0, 1]), (12, [1, 2, 0, 0, 1, 0, 1, 0]), (13, [2]),
     (14, [1, 2, 0, 0, 1, 0, 1, 0, 1]), (15, [2, 0, 0, 1, 0, 1, 0])]

@[noinline, expose] def conjOK : Bool :=
  let E₁ := enumBFS 42 (wordTabs wP₁) 960
  let E₂ := enumBFS 42 (wordTabs wP₂) 960
  conjP1Data.all (fun d => found (indexOf E₁.tabs) E₁.tabs (wordTab d.2) && invOK (wordTab d.2) &&
    conjTab 42 (wordTab d.2) (invTab 42 (wordTab d.2)) (tgT d.1) == tgT 4) &&
  conjP2Data.all (fun d => found (indexOf E₂.tabs) E₂.tabs (wordTab d.2) && invOK (wordTab d.2) &&
    conjTab 42 (wordTab d.2) (invTab 42 (wordTab d.2)) (tgT (4 * d.1)) == tgT 4)

end CFSG.ComponentClassification.GrSLit.L34Facts
