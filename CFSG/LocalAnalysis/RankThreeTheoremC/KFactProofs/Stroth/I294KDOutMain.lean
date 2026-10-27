module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutD4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutE6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerD4
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbedding.TwoGenInner (PGoodOut pGoodOut_of_not_dvd_outer pGoodOut_of_catalogGroup
  d4PGood)
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

section Heavy


theorem pGoodOut_ge_five_of_not_linearOrUnitary {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hnab : ∃ a b : L, a * b ≠ b * a) (hcat : IsCatalogGroup L) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hLU : ¬ IsLinearOrUnitaryAt p L) : PGoodOut p L := by
  refine pGoodOut_of_catalogGroup hnab hcat hp hp5 ?_ ?_ d4PGood
  · intro n ℓ f hcl hdvd
    exact hLU (isLinearOrUnitaryAt_of_psl hcl (hdvd.trans (Nat.gcd_dvd_left _ _))
      (hdvd.trans (Nat.gcd_dvd_right _ _)))
  · intro n ℓ f hcl hdvd
    exact hLU (isLinearOrUnitaryAt_of_psu hcl (hdvd.trans (Nat.gcd_dvd_left _ _))
      (hdvd.trans (Nat.gcd_dvd_right _ _)))

theorem pGoodOut_three_or_of_catalog (hD4 : D4ThreeRankFour) (hE6 : E6ThreeRankFour)
    (hT : TwistedE6ThreeRankFour) {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hnab : ∃ a b : L, a * b ≠ b * a) (hcat : IsCatalogGroup L) :
    PGoodOut 3 L ∨ IsLinearOrUnitaryAt 3 L ∨ 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  rcases PlaneCases.catalog_cases (TCB.tauCetiCatalogBridge L hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · refine Or.inl (pGoodOut_of_not_dvd_outer Nat.prime_three ?_)
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 3 Nat.prime_three
      (by norm_num)
  · exact pGoodOut_three_or_of_lieModel hD4 hE6 hT hadm hmodel
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    have hnd := CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s 3 Nat.prime_three
      (by norm_num)
    refine Or.inl (pGoodOut_of_not_dvd_outer Nat.prime_three ?_)
    rw [Nat.card_congr (equivalence (e.trans e')).toEquiv]
    exact hnd

theorem kDOutDerived_of_threeRank (hD4 : D4ThreeRankFour) (hE6 : E6ThreeRankFour)
    (hT : TwistedE6ThreeRankFour) : KDOutDerived := by
  intro p hp hp2 L _ _ hs hnab hcat _ α hαp hαc hαi
  haveI : IsSimpleGroup L := hs
  by_cases hLU : IsLinearOrUnitaryAt p L
  · exact Or.inl hLU
  · by_cases hp3 : p = 3
    · subst hp3
      rcases pGoodOut_three_or_of_catalog hD4 hE6 hT hnab hcat with h | h | h
      · exact absurd (pElement_mem_inner_of_pGoodOut hp h hαp hαc) hαi
      · exact absurd h hLU
      · exact Or.inr ⟨rfl, h⟩
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      exact absurd (pElement_mem_inner_of_pGoodOut hp
        (pGoodOut_ge_five_of_not_linearOrUnitary hnab hcat hp hp5 hLU) hαp hαc) hαi

theorem kDOutDerived_holds : KDOutDerived :=
  kDOutDerived_of_threeRank d4ThreeRankFour_holds e6ThreeRankFour_holds
    twistedE6ThreeRankFour_holds

end Heavy

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
