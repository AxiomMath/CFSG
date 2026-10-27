module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Simple
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.KDSp6

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.SectionRank

theorem solomonA12InputK_of_inputs (hSch : SchreierFor Catalog) (hP : P12Facts) (hSp6 : KDSp6) :
    SolomonA12InputK := by
  intro K _ _ hKg hK
  haveI : IsSimpleGroup K := isSimpleGroup_of_hyp hSch hP hKg hK
  exact hSp6 K (KCore.KGroupAllSimple.catalogue_self catalog_isoInvariant hKg) hK

end CFSG.EvenSporadicStandard.M12Std.SolomonK
