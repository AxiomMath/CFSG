module

public import CFSG.CGT.PushingUpLit.CGT6K1.Defs
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatDispatch
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatAlternating
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOdd
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatEven
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadic

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG.LocalAnalysis.EvenBN.GMSK


theorem catSelector_holds : CatSelector :=
  catalog_selector fixedRootSelector_alternating fixedRootSelector_oddLieType
    fixedRootSelector_evenLieType Sporadic.fixedRootSelector_sporadicRep

end CFSG.CGT.PushingUpLit.CGT6K1
