module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL4U4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL4U4UD

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

theorem cf23L4U4O8Comp_holds : CF23L4U4O8Comp := by
  intro N _ _ p f hp hp2 hf hN G hInn α J hα hJN hJc hJ hstd hodd hsmall
  rcases hN with hN | hN | ⟨e, rfl, hN⟩
  · exact cf23L4U4O8Comp_psl4 hp hp2 hf hN G hInn α J hα hJN hJc hJ hstd hodd hsmall
  · exact cf23L4U4O8Comp_psu4_holds hp hp2 hf hN G hInn α J hα hJN hJc hJ hstd hodd hsmall
  · exact cf23L4U4O8Comp_minus8 hp hp2 (by omega) hN G hInn α J hα hJN hJc hJ hstd hodd hsmall

end CFSG.ComponentClassification.GSThmB.Cov
