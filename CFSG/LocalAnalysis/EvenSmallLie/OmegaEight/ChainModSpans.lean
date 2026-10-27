module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainModData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1CohSpans

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open CFSG.EvenSmallLie.UnitarySix.YamadaPar Stage1

@[expose] def endSpans (ε : Eps) : Prop :=
  CertSpans 36 1 (6 * 36) (linBits 36 (6 * 36) (cobFb6 ε)) #[packN 6 1 fun _ => id6]

@[expose] def modSpans (ε : Eps) : Prop :=
  CertSpans (7 * 36) 6 (36 * 36) (linBits (7 * 36) (36 * 36) (modFb ε))
    (Array.ofFn (n := 6) fun m => modSol ε m)

end CFSG.EvenSmallLie.OmegaEight.Chain
