module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoCentralCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7Std

public section

namespace CFSG.ComponentClassification.CatFactsSp4

theorem cfSp4TwoCentral : GSThmB.CFSp4TwoCentral :=
  fun H _ _ p f hp hp2 hf h5 hs hY a ha J hJY hJa hJ hJm R hR2 hRle hRs =>
    twoCentral_main H p f hp hp2 hf h5 hs hY a ha J hJY hJa hJ hJm R hR2 hRle hRs

end CFSG.ComponentClassification.CatFactsSp4
