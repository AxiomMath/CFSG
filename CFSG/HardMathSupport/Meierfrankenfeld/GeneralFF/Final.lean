module

public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.Assembly
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusion

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

theorem citedFFL34BestOffender_of_l34
    (hL34 : Coordinator.L34ExclusionProp) : AGLEmbedding.CitedFFL34BestOffender :=
  Coordinator.citedFFL34BestOffender_of oddPrimeCoreExclusion componentSectionProp hL34

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
