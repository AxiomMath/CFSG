module

public import CFSG.LocalAnalysis.StandardType.GGTwE6R5Holds
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.E6Model

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3

open CFSG.Open


theorem card_le_of_lieModel_twistedE6_two {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .twistedE6 0 2 1) (E : Subgroup X) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, hK, σ, hσ, he⟩ := CFSG.EvenSporadicStandard.Induction.twistedE6_model_data h
  have hm : CFSG.Blueprint.TwistedChevalleyModel X .E6 (2 ^ 1) := by
    unfold CFSG.Blueprint.TwistedChevalleyModel
    exact ⟨K, inferInstance, inferInstance, hK, σ, hσ, he⟩
  obtain ⟨L, _, _, τ, hL, hτ, ⟨e₁⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two le_rfl hm
  obtain ⟨ε, -⟩ := CFSG.StandardType.TwE6DD2.exists_recipeEquiv le_rfl hL τ hτ
  by_contra hlt
  rw [not_le] at hlt
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hE.isPGroup
  have h6 : 3 ^ 6 ≤ Nat.card E := by
    rw [hk] at hlt ⊢
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt)
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hE.isPGroup h6
  let φ := (e₁.trans ε).toMonoidHom
  refine CFSG.StandardType.ggTwE6ThreeNoRankSixInput_holds L 1 le_rfl hL (by norm_num)
    (by norm_num) ((T.map E.subtype).map φ) ((hE.mono (Subgroup.map_subtype_le T)).map φ) ?_
  rw [Subgroup.card_map_of_injective (e₁.trans ε).injective,
    Subgroup.card_map_of_injective E.subtype_injective, hT]

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3
