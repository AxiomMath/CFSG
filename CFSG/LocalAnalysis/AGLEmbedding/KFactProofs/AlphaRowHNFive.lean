module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Certificate9604

public section

namespace CFSG.AGLEmbedding

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.AlphaHNRank

theorem rankLiftDatum_HN_five :
    RankLiftDatum NativeSporadic.HN 5 :=
  rankLiftDatum_of_check (specP 5 133) (D := hnrlSpec) Nat.prime_five
    Certificates.certificate9604

end CFSG.AGLEmbedding
