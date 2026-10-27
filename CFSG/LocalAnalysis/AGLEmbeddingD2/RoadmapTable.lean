module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapFamilies
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicRows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GuestThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Tits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open
open CFSG.AGLEmbedding


theorem d2_of_table_leaves (hS : D2SeitzCross) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner)
    (hS3 : D2PairStrongThree)
    (hMcL : D2HeisLocalAt (.sporadic .McL) fun p => p = 5)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusLocalAt (.lie d) fun p => p = 5)
    (hKFT : KFactTitsThreeCore)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => ((IsD2SeitzException p d.1 ∧ ¬ (p = 3 ∧
        ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
          (d.1 = .twistedA 3 q ∨ d.1 = .B 3 q ∨ d.1 = .B 4 q))) ∧
        ¬ CFSG.LocalAnalysis.RankThreeTheoremC.IsD2SeitzLTwoEight p d.1 ∧
        ¬ (d.1 = .tits ∧ p = 5)) ∧ ¬ (d.1 = .tits ∧ p = 3))
    (hrows : D2SporadicOpenRows) (hMon : D2IndexCaseAt (.sporadic .M) fun _ => True)
    (hKFM11 : KFactM11Three) (hKF22 : KFactFi22GuestThree)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M := by
  have htits : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => d.1 = .tits ∧ p = 3 := by
    intro d G' _ _ hglob hD1' q hq
    exact d2IndexCaseAt_tits_three hKFT d hq.1 G' hglob hD1' q hq.2
  exact d2_of_family_leaves hS h84 h85 h86 h93 hCGT hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p hKB hKS
    hS3 (d2HeisBorelAt_of_local hMcL) (d2HeisBorelAt_of_local hJ4)
    (fun d hd => d2TorusBorelAt_of_local (hTits d hd))
    (fun d => d2IndexCaseAt_of_split (hexc d) (htits d))
    (d2SporadicCase_of_openRows hrows hMon (d2IndexCaseAt_m11_three hKFM11 h84 hD2 hS3)
      (d2IndexCaseAt_fi22_five hKF22))
    G hnonab hK hchar he hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ hQrank hQM H hH hQH

theorem d2_of_table_leaves' (hS : D2SeitzCross) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner)
    (hS3 : D2PairStrongThree)
    (hMcL : D2HeisLocalAt (.sporadic .McL) fun p => p = 5)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusLocalAt (.lie d) fun p => p = 5)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => ((IsD2SeitzException p d.1 ∧ ¬ (p = 3 ∧
        ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
          (d.1 = .twistedA 3 q ∨ d.1 = .B 3 q ∨ d.1 = .B 4 q))) ∧
        ¬ CFSG.LocalAnalysis.RankThreeTheoremC.IsD2SeitzLTwoEight p d.1 ∧
        ¬ (d.1 = .tits ∧ p = 5)) ∧ ¬ (d.1 = .tits ∧ p = 3))
    (hrows : D2SporadicOpenRows) (hMon : D2IndexCaseAt (.sporadic .M) fun _ => True)
    (hKFM11 : KFactM11Three) (hKF22 : KFactFi22GuestThree)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M :=
  d2_of_table_leaves hS h84 h85 h86 h93 hCGT hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p hKB hKS hS3 hMcL
    hJ4 hTits kFactTitsThreeCore hexc hrows hMon hKFM11 hKF22 G hnonab hK hchar he hδ₁ hδ₂ hD1 p
    hp P M hM' hPM Q hQ hQrank hQM H hH hQH

theorem d2_of_table_leaves'' (hS : D2SeitzCross) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner)
    (hS3 : D2PairStrongThree)
    (hMcL : D2HeisLocalAt (.sporadic .McL) fun p => p = 5)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => ((IsD2SeitzException p d.1 ∧ ¬ (p = 3 ∧
        ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
          (d.1 = .twistedA 3 q ∨ d.1 = .B 3 q ∨ d.1 = .B 4 q))) ∧
        ¬ CFSG.LocalAnalysis.RankThreeTheoremC.IsD2SeitzLTwoEight p d.1 ∧
        ¬ (d.1 = .tits ∧ p = 5)) ∧ ¬ (d.1 = .tits ∧ p = 3))
    (hrows : D2SporadicOpenRows) (hMon : D2IndexCaseAt (.sporadic .M) fun _ => True)
    (hKFM11 : KFactM11Three) (hKF22 : KFactFi22GuestThree)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M :=
  d2_of_table_leaves' hS h84 h85 h86 h93 hCGT hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p hKB hKS hS3 hMcL
    hJ4 (fun d hd => d2TorusLocalAt_tits d hd) hexc hrows hMon hKFM11 hKF22 G hnonab hK hchar he
    hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ hQrank hQM H hH hQH

end CFSG.AGLEmbeddingD2
