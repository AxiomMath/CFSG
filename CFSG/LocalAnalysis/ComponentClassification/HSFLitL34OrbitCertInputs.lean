module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34CertInputs

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

@[expose] def cosetClassOK (TR T0 : List ℕ) : Bool :=
  let Z := T0.filter (inZB T0)
  TR.all fun y => !(isId (psq y)) || inZB T0 y ||
    (let cs := T0.map fun t => pcomp (pcomp t y) (pcube t)
     !(cs.all (commC y)) || Z.all fun z => memB (pcomp y z) cs)

end CFSG.ComponentClassification.HSFLit.AutL34
