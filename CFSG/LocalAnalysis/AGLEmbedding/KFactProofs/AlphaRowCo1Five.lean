module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9603

public section

namespace CFSG.AGLEmbedding

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.AlphaCo1Rank

theorem rankLiftDatum_Co1_five :
    RankLiftDatum NativeSporadic.Co1 5 :=
  rankLiftDatum_of_check (spec2 24) (D := co1rlSpec) Nat.prime_five
    Certificates.certificate9603

end CFSG.AGLEmbedding
