module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SMain
public import CFSG.ClassicalInvolution.Q3.Q3VF4SAdaptModel
public import CFSG.ClassicalInvolution.Q3.Q3VF4SRow
public import CFSG.ClassicalInvolution.Q3.Q3VF4SPart
public import CFSG.ClassicalInvolution.Q3.Q3VF4CClose
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S


theorem chainPiece3F4_proved (hP : Q3TC.ProductP1Input3) : ChainPiece3F4 :=
  chainPiece3F4_of_model f4Row3 f4PartnerFact3 hP

theorem sp3F4NoncommInput_proved_of_product
    (hP : Q3TC.ProductP1Input3) : Chain3.Sp3F4NoncommInput :=
  sp3F4NoncommInput_proved (chainPiece3F4_proved hP)

theorem piece3Sp3_of_product
    (h3 : Q3W.OddThreeFreeInput) (hP : Q3TC.ProductP1Input3) : Q3W.Piece3Sp3 :=
  Chain3.piece3Sp3_of_noncomm h3 (sp3F4NoncommInput_proved_of_product hP)

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
