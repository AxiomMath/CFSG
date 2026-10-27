module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XCerts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

section Cert


theorem autExtOpen_holds : AutExtOpen :=
  ⟨xInnerFacts_holds, xCentFacts_holds⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section4
