module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankLift
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankLyLift
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9603
public import Certificates.Certificate9605
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.SectionRank CFSG.Blueprint CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo1Rank
  CFSG.AGLEmbedding.R3.AlphaLyRank

theorem three_le_pRank_Co1_five
    [Finite (NativeSporadic.Carrier .Co1)] :
    3 ≤ Open.pRank 5 (⊤ : Subgroup (NativeSporadic.Carrier .Co1)) := by
  have : Finite NativeSporadic.Co1 := ‹Finite (NativeSporadic.Carrier .Co1)›
  exact three_le_pRank_of_rlCheck (spec2 24) (D := co1rlSpec) Nat.prime_five
    Certificates.certificate9603 (m := co1rlMods[0]'(by decide))
    (List.getElem_mem _) (by decide)

theorem three_le_pRank_Ly_five
    [Finite (NativeSporadic.Carrier .Ly)] :
    3 ≤ Open.pRank 5 (⊤ : Subgroup (NativeSporadic.Carrier .Ly)) := by
  have : Finite NativeSporadic.Ly := ‹Finite (NativeSporadic.Carrier .Ly)›
  exact three_le_pRank_of_rlLyCheck (specP 5 111) (D := lyrlSpec) Nat.prime_five
    Certificates.certificate9605 (m := lyrlMods[0]'(by decide))
    (List.getElem_mem _) (by decide)

end CFSG.AGLEmbeddingD2
