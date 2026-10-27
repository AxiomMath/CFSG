module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeFinal
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLSpFourFinal

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

theorem citedBlockTransvectionPLType_holds :
    CFSG.AGLEmbedding.CitedBlockTransvectionPLType :=
  Coordinator.citedBlockTransvectionPLType_of_spFour
    Coordinator.PLType.spFourTransvectionCent_holds

end CFSG.HardMathSupport.Curtis.UnitaryLevi
