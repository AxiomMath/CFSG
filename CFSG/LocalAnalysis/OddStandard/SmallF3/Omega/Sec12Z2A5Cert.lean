module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Core
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatDispatch
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOdd
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatEven
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LocalAnalysis.EvenBN.GMSK


theorem asc82Z2A5K_holds : Asc82Z2A5K :=
  asc82Z2A5K_of (catalog_selector fixedRootSelector_alternating fixedRootSelector_oddLieType
    fixedRootSelector_evenLieType Sporadic.fixedRootSelector_sporadicRep)

end CFSG.OddStandard.SmallF3.Omega
