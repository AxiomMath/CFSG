module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

@[expose] def liftW0 : List (Fin 2 × Bool) := tw 4 ++ zOne ++ zTwo

@[expose] def liftSpecs : List (List (Fin 2 × Bool) × ℕ × ℕ × ℕ) :=
  [(FreeGroup.invRev liftW0 ++ alphaF liftW0, 0, 0, 2),
    (FreeGroup.invRev liftW0 ++ alphaG liftW0, 0, 0, 2),
    (FreeGroup.invRev liftW0 ++ alphaU liftW0, 0, 0, 0), (wpow liftW0 2, 0, 0, 1)]

@[expose] def liftNormOK : Bool :=
  let ET := enumBFS 42 (wordTabs wT₀) 64
  let iT := indexOf ET.tabs
  (allBelow 64 fun k => found iT ET.tabs (conjTab 42 r₂T r₂T (wordTab (tg k))) &&
    found iT ET.tabs (conjTab 42 r₃T r₃T (wordTab (tg k)))) &&
    comp 42 r₂T r₃T == comp 42 r₃T r₂T

end CFSG.ComponentClassification.GrSLit.L34Facts
