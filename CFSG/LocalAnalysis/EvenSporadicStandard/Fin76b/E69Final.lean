module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69J2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69J3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

theorem fin76bEFacts69 :
    Fin76bEFacts69 := by
  intro G _ _ L z t T₀ E Q x β B hconf
  rcases hconf.sporadic with hL | hL
  · exact J2.eFacts69_of_isSporadic hconf.cfg hconf.econfig hL
  · exact J3.eFacts69_of_isSporadic hconf.cfg hconf.econfig hL

end CFSG.EvenSporadicStandard.Fin76b
