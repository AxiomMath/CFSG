module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Final
public import CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.L34Exclusion

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

theorem citedFFL34BestOffender :
    AGLEmbedding.CitedFFL34BestOffender :=
  GeneralFF.citedFFL34BestOffender_of_l34 L34Offender.l34ExclusionProp

end CFSG.HardMathSupport.Meierfrankenfeld.Coordinator
