module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4GamData

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.J4.Native
  CFSG.Quasithin.J4M2

@[expose] def rrGen (g : ℕ) : Array V2 := if g = 0 then cArows else if g = 1 then cBrows else cZrows

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
