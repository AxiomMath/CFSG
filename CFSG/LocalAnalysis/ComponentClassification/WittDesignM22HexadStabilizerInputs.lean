module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import Certificates.Certificate2195
public import Certificates.Certificate2031
public import Certificates.Certificate2035

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction
open scoped Pointwise

@[expose] def hexadD0 : Finset (Fin 22) := {3, 4, 5, 12, 15, 20}

@[expose] def hexadT0 : Finset (Fin 22) := {0, 1, 3, 6, 14, 20}

end CFSG.ComponentClassification.WittDesign
