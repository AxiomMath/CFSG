module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2CertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def nonElemData : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [(17, 8, 2, 0, 0), (27, 8, 0, 2, 0)]

@[noinline, expose] def nonElemOK : Bool := nonElemData.all fun d => commData2.contains d

end CFSG.ComponentClassification.GrSLit.L34Facts
