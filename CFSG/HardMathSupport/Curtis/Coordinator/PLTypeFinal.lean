module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAssembly
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeOrthCent
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeOrthTwoPart
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAlt
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeFactsOrth
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeFactsSpB
public import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SpSmall
public import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SymCent

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open PLType

theorem citedBlockTransvectionPLType_of_spFour
    (hSp : SpFourTransvectionCent) :
    CFSG.AGLEmbedding.CitedBlockTransvectionPLType :=
  citedBlockTransvectionPLType_of_cells OrthCent.orthTransvectionCent_holds
    CFSG.HardMathSupport.RichardWeiss.Proving.PLType.symTransvectionCent_holds hSp
    orthTwoPart_holds tauCetiOrthFacts_holds altTypeExcl_holds spTypeB_holds
    CFSG.HardMathSupport.RichardWeiss.Proving.PLType.spSmall_holds

end CFSG.HardMathSupport.Curtis.Coordinator
