module

public import CFSG.ClassicalInvolution.Asc77.AscC22P17
public import CFSG.ClassicalInvolution.Phan.PhanD13Final

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace W14

set_option linter.unusedSectionVars false

section Proofs

variable {p f : ℕ} [Fact p.Prime]

theorem chain22X_of_phan (hG : PhanD4.PhanD4Geometry p f) (hC : R31.C22_phanChainNeg p f) :
    C22_chainSettingX p f :=
  R31.c22_chainSettingX_of_recog c22_chainPos_proved
    (R31.c22_recogNeg_of_phan (PhanD4.phanD4Recognition_of_geometry hG) hC)

end Proofs

end W14

end CFSG.ClassicalInvolution.Asc77
