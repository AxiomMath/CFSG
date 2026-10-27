module

public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open CFSG.Open

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def glNaturalRep (n : ℕ) (K : Type) [Field K] :
    Representation K (GL (Fin n) K) (Fin n → K) :=
  (Units.coeHom (Module.End K (Fin n → K))).comp
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)).toMonoidHom

@[expose] noncomputable def slNaturalRep (n : ℕ) (K : Type) [Field K] :
    Representation K (StatedSL n K) (Fin n → K) :=
  (glNaturalRep n K).comp (StatedSL n K).subtype

end CFSG.HardMathSupport.GuralnickMalle
