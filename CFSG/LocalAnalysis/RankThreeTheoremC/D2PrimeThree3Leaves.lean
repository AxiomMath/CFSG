module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PrimeThree3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2U3Case3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

@[expose] def D2U3ThreeStrong3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    D2IndexCaseStrongAt3 G (.lie d) fun p => p = d.1.characteristic ∧ p = 3

@[expose] def D2AltSixStrong3 (G : Type) [Group G] [Finite G] : Prop :=
  D2IndexCaseStrongAt3 G (.alternating 6 (by norm_num)) fun p => p = 3

theorem d2PairAt_u3 {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) :
    D2PairAt (.lie d) fun p => p = d.1.characteristic ∧ p = 3 := by
  rintro X _ _ p ⟨hpc, -⟩ R A X₀ K hK ⟨e⟩
  have : Fact p.Prime := ⟨hK.prime⟩
  obtain ⟨hdu, hnu⟩ := isUnitaryIndex_of_case hpc hd
  exact hK.primeComplementCore_eq_bot_of_u3 unitaryBorelKFacts.sylowStructure
    unitaryBorelKFacts.unipotentCentralizer unitaryBorelKFacts.borelMaximal hdu hnu e

theorem d2U3Three3_of_strong (h84 : Asc81bEightFour) (hX : D1NoXBlock3 G)
    (h : D2U3ThreeStrong3 G) : D2U3Three3 G :=
  fun d hd => d2IndexCaseAt3_of_pair (fun _ hp => hp.2) (d2PairAt_u3 hd) h84 hX (h d hd)

theorem d2U3ThreeStrong3_of_u3Three3 (h : D2U3Three3 G) : D2U3ThreeStrong3 G :=
  fun d hd => d2IndexCaseStrongAt3_of_indexCaseAt3 (h d hd)

theorem d2AltSixCase3_of_strong (h84 : Asc81bEightFour) (hX : D1NoXBlock3 G)
    (h : D2AltSixStrong3 G) : D2AltSixCase3 G :=
  d2IndexCaseAt3_of_pair (fun _ hp => hp) d2PairAt_altSix h84 hX h

theorem d2AltSixStrong3_of_altSixCase3 (h : D2AltSixCase3 G) : D2AltSixStrong3 G :=
  d2IndexCaseStrongAt3_of_indexCaseAt3 h

end CFSG.LocalAnalysis.RankThreeTheoremC
