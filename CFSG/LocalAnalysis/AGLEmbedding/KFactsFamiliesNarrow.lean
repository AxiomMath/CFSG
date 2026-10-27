module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BetaRank3
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def BetaLieCyclic : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K, (T : Subgroup K) ≠ ⊥ →
      IsCyclic (T : Subgroup K) → Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

@[expose] def RankOneAutFactsFamilies : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ d : TauCeti.ValidLieTypeIndex,
      ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨
        (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨ IsReeGTwoIndex p d) →
      Nonempty (K ≃* CatGroup d) → RankOneLieAutFacts p K

theorem betaLieCyclic_of_outCyclic (hOut : LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) :
    BetaLieCyclic := by
  intro K _ _ hs hnab d he p hp hp2 T _ hTc
  obtain ⟨e⟩ := he
  exact LocalAnalysis.RankThreeTheoremC.pRank_mulAut_le_two_of_isCyclic_sylow hp
    (center_eq_bot_of_isSimpleGroup_of_nonabelian hs hnab) T hTc
    (hOut K hs hnab ⟨.lie d, ⟨e⟩⟩ p hp hp2 T hTc)

theorem kFactBetaLie_of_rankOneFamilies (hId : KFactOneLieIdent) (hC : BetaLieCyclic)
    (hR : RankOneAutFactsFamilies) : KFactBetaLie := by
  intro K _ _ hs hnab d he p hp hp2 T hT hcase
  by_cases hTc : IsCyclic (T : Subgroup K)
  · exact Or.inl (hC K hs hnab d he p hp hp2 T hT hTc)
  by_cases hrk : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2
  · exact Or.inl hrk
  obtain ⟨e⟩ := he
  obtain ⟨d', hd', he'⟩ :=
    hId K hs hnab ⟨.lie d, ⟨e⟩⟩ p hp hp2 T hTc (hcase.resolve_left hTc) hrk
  exact Or.inr (hR K p hp hp2 d' hd' he')

end CFSG.AGLEmbedding
