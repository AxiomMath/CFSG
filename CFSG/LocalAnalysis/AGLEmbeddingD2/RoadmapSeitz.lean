module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapTable
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.M11Three
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzRest
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34OnlyThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFi22GuestThree

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding


theorem d2_of_seitz_leaves (hS : D2SeitzCross) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner)
    (hS3 : D2PairStrongThree)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (hβ : D2L34BetaCase)
    (hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2IndexCaseAt (.lie d) fun p => p = 5)
    (hrows : D2SporadicOpenRows) (hMon : D2IndexCaseAt (.sporadic .M) fun _ => True)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M := by
  have hOnly : D2OnlyL34Three := d2OnlyL34Three_of kFactLieCharRank hS
    (d2AltSixCase_of_strong h84 hD2 (d2IndexCaseStrongAt_altSix_of_pairStrong hS3))
    (d2U3Three_of_strong
      (d2U3ThreeStrong_of (d2IndexCaseStrongAt_u3_of_pairStrong unitaryBorelKFacts hS3))
      unitaryBorelKFacts h84 hD2)
    (d2IndexCaseAt_l28_of_pairStrong kFactCatalogSchreier h84 hD2 hS3)
    (fun d hd => d2IndexCaseAt_tits_three kFactTitsThreeCore d hd)
    fun s => (d2SporadicCase_of_openRows hrows hMon
      (d2IndexCaseAt_m11_three kFactM11Three h84 hD2 hS3)
      (d2IndexCaseAt_fi22_five kFactFi22GuestThree) s).mono fun p hp =>
        ⟨fun h => by have := h.2; omega, fun h => by have := h.2; omega⟩
  exact d2_of_table_leaves'' hS h84 h85 h86 h93 hCGT hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p hKB hKS hS3
      d2HeisLocalAt_mcl hJ4
      (d2SeitzRest_of_l34_sz kFactL34Outer kFactL34Inner hβ hOnly h84 hD2 hS3 hSz) hrows hMon
      kFactM11Three kFactFi22GuestThree G hnonab hK hchar he hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ
      hQrank hQM H hH hQH

end CFSG.AGLEmbeddingD2
