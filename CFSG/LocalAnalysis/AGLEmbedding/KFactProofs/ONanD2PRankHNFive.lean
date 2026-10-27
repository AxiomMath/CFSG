module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankLift
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Certificate9630

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.SectionRank CFSG.Blueprint CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaHNE125

theorem three_le_pRank_HN_five
    [Finite (NativeSporadic.Carrier .HN)] :
    3 ≤ Open.pRank 5 (⊤ : Subgroup (NativeSporadic.Carrier .HN)) := by
  have : Finite NativeSporadic.HN := ‹Finite (NativeSporadic.Carrier .HN)›
  exact three_le_pRank_of_nmodCheck (specP 5 133) (m := hnE125Mod) Nat.prime_five
    Certificates.certificate9630.1 Certificates.certificate9630.2 (by decide)

end CFSG.AGLEmbeddingD2
