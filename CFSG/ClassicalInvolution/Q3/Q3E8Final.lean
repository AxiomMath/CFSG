module

public import CFSG.ClassicalInvolution.Q3.Q3E8Rows
public import CFSG.ClassicalInvolution.Q3.Q3E8TorNodes
public import CFSG.ClassicalInvolution.Q3.Q3E7MSign
public import CFSG.ClassicalInvolution.Q3.Q3E7MStar
public import CFSG.ClassicalInvolution.Q3.Q3E7MD8
public import CFSG.ClassicalInvolution.Q3.Q3E8BF5
public import CFSG.ClassicalInvolution.Q3.Q3E8BMain
public import CFSG.ClassicalInvolution.Q3.Q3E8BRow
public import CFSG.ClassicalInvolution.Q3.Q3E8BP1x
public import CFSG.ClassicalInvolution.ModelFacts.E8D8Conn
public import CFSG.ClassicalInvolution.ModelFacts.E8D8Adj
public import CFSG.ClassicalInvolution.Q3.Q3TCPartner
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD

set_option linter.unusedSectionVars false



theorem piece3E8_of_inputs (h3 : OddThreeFreeInput) (hP1x : Q3TC.ProductP1Input3)
    (hTor : ToralStdE73) : Piece3E8 :=
  piece3E8_of_facts h3 e7SignPerp3 (e8PartnerToral3_of hTor) e7FrameRelations3
    e7FrameInvolutions3 e7PerpA2StarFree3 e7LayerEquiv3 (TypeE8.fund12Connected 3 1 le_rfl)
    e8D8Row3 d8NoThreeAdj3 (e8P1x3_of_productP1 hP1x) e8R2Excluded3

end CFSG.ClassicalInvolution.Q3.Q3W
