module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLieCharRankProof
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactSeitzRankThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzLTwoEight
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeOrFiveDvd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open
open CFSG.AGLEmbedding

theorem d2_of_family_leaves (hS : D2SeitzCross) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner)
    (hS3 : D2PairStrongThree)
    (hMcL : D2HeisBorelAt (.sporadic .McL) fun p => p = 5)
    (hJ4 : D2HeisBorelAt (.sporadic .J4) fun p => p = 11)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusBorelAt (.lie d) fun p => p = 5)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => (IsD2SeitzException p d.1 ∧ ¬ (p = 3 ∧
        ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
          (d.1 = .twistedA 3 q ∨ d.1 = .B 3 q ∨ d.1 = .B 4 q))) ∧
        ¬ CFSG.LocalAnalysis.RankThreeTheoremC.IsD2SeitzLTwoEight p d.1 ∧
        ¬ (d.1 = .tits ∧ p = 5))
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt (.sporadic s) fun p => ¬ (s = .McL ∧ p = 5) ∧ ¬ (s = .J4 ∧ p = 11))
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M := by
  let HB : TauCeti.CFSGIndex → ℕ → Prop := fun i p =>
    (i = .sporadic .McL ∧ p = 5) ∨ (i = .sporadic .J4 ∧ p = 11)
  let TB : TauCeti.CFSGIndex → ℕ → Prop := fun i p =>
    ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .tits ∧ p = 5
  let RK : TauCeti.CFSGIndex → ℕ → Prop := fun i p => p = 3 ∧ ∃ d : TauCeti.ValidLieTypeIndex,
    i = .lie d ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
      (d.1 = .twistedA 3 q ∨ d.1 = .B 3 q ∨ d.1 = .B 4 q)
  have hHB : ∀ i, D2HeisBorelAt i (HB i) := by
    intro i X _ _ p hp R A X₀ K hK he
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hMcL X 5 rfl R A X₀ K hK he
    · exact hJ4 X 11 rfl R A X₀ K hK he
  have hHB5 : ∀ i p, HB i p → 5 ≤ p := by
    rintro i p (⟨-, rfl⟩ | ⟨-, rfl⟩) <;> norm_num
  have hTB : ∀ i, D2TorusBorelAt i (TB i) := by
    rintro i X _ _ p ⟨d, rfl, hd, rfl⟩ R A X₀ K hK he
    exact hTits d hd X 5 rfl R A X₀ K hK he
  have hTB5 : ∀ i p, TB i p → 5 ≤ p := by
    rintro i p ⟨-, -, -, rfl⟩
    norm_num
  have hRK : ∀ (i : TauCeti.CFSGIndex) (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* i.Group) → ∀ p, RK i p → 3 ≤ Open.pRank p (⊤ : Subgroup K) := by
    intro i K _ _ ⟨e⟩ p ⟨hp3, d, hid, hq⟩
    subst hp3 hid
    exact kFactSeitzRankThreeExceptions K d hq ⟨e⟩
  refine d2_of_all'' kFactLieCharRank hS kFactCatalogSchreier kFactThreeOrFiveDvd h84 h85 h86 h93
    hCGT hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p
    (d2AltFive_of_block kFactThreeOrFiveDvd kFactCatalogSchreier h84 h85 h86 h93 hD2 hK2 hC3 hK5
      (d2AltFiveBlock_of kFactThreeOrFiveDvd kFactCatalogSchreier h84 h85 h86 h93 hD2 hK2 hC3 hK5
        hKB hKS))
    (d2IndexCaseStrongAt_altSix_of_pairStrong hS3)
    (d2U3ThreeStrong_of (d2IndexCaseStrongAt_u3_of_pairStrong unitaryBorelKFacts hS3))
    HB hHB hHB5 TB hTB hTB5 RK hRK ?_ ?_ G hnonab hK hchar he hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ
    hQrank hQM H hH hQH
  · intro d
    refine d2IndexCaseAt_of_split (Q := fun p =>
      CFSG.LocalAnalysis.RankThreeTheoremC.IsD2SeitzLTwoEight p d.1) ?_
      (fun G _ _ hglob hD1 p hp => d2IndexCaseAt_l28_of_pairStrong kFactCatalogSchreier h84 hD2 hS3
        d G hglob hD1 p hp)
    rintro G _ _ hglob hD1 p ⟨⟨hexcp, -, hTBp, hRKp⟩, hL28⟩
    exact hexc d G hglob hD1 p ⟨⟨hexcp, fun h => hRKp ⟨h.1, d, rfl, h.2⟩⟩, hL28,
      fun h => hTBp ⟨d, rfl, h.1, h.2⟩⟩
  · rintro s G _ _ hglob hD1 p ⟨hHBp, -, -⟩
    exact hSpor s G hglob hD1 p ⟨fun h => hHBp (Or.inl ⟨by rw [h.1], h.2⟩),
      fun h => hHBp (Or.inr ⟨by rw [h.1], h.2⟩)⟩

end CFSG.AGLEmbeddingD2
