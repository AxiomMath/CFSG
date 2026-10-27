module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Pair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PerfectCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduction

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding

structure PairStrongCtx {G : Type} [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) : Prop where
  glob : D2Global G
  d1 : D1For G
  esc : D2Escape 3 P M A H R
  max : D2EscapeMax 3 P M R
  beta : 3 ∈ GLBBetaFour G
  pair : AGLPair 3 M H R
  strong : GLBStronglyEmbedded 3 M
  perf : D2PerfectThreePrime H M

end CFSG.AGLEmbeddingD2.McLaughlin
