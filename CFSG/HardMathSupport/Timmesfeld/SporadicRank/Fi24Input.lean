module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi24Data

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi24

@[expose] def fi24Matrices : List (List Nat) :=
  wordsL 3 7 (fi24Tidx.map fun i => (fi24Mod.acts.getD i default).mat)

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
