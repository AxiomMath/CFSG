module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSData

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.GLQ CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

@[expose] def jsQn : Pair := mulP (powP QXn 8) (powP QYn 4)

@[noinline, expose] def centralOK : Bool :=
  O.eq (mulP jsJn jsJn).1 O.one && O.eq (mulP jsSn jsSn).1 O.one &&
    O.eq (mulP jsSn jsQn).1 (mulP jsQn jsSn).1

end CFSG.Sporadic.J4Schreier
