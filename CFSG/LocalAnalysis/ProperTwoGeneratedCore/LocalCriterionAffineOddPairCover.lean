module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPairRank
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {Y F K : Type*} [Group Y] [Group F] [Group K]

theorem elementary_binary_quotient_card_le_four [Finite Y] [Finite K]
    (hno : ∀ V : Subgroup Y, ¬ IsKleinFour V) (hp : IsPGroup 2 Y)
    [IsElementaryAbelian 2 K] (f : Y →* K) (hf : Function.Surjective f) :
    Nat.card K ≤ 4 := by
  obtain ⟨s, hs, hcard⟩ := CFSG.LargeEvenClassification.Helpers.rank_one_two_group_two_generators
    hp (no_four_group_two_rank_le_one hno hp) (⊤ : Subgroup Y)
  have hrank : Group.rank Y ≤ 2 := by
    have htop := (Group.rank_le hs).trans hcard
    have hmap := Group.rank_le_of_surjective (⊤ : Subgroup Y).subtype
      (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)
    exact hmap.trans htop
  have hKrank : CFSG.generatorRank K ≤ 2 := by
    rw [CFSG.generatorRank_eq_group_rank]
    exact (Group.rank_le_of_surjective f hf).trans hrank
  rw [CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := 2) K]
  exact (pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) hKrank).trans (by norm_num)

theorem normal_binary_image_has_actual_two_group_cover [Finite Y]
    (π : Y →* F) (hπ : Function.Surjective π)
    (Q : Subgroup F) [Q.Normal] (hQ : IsPGroup 2 Q) :
    ∃ R : Subgroup Y, IsPGroup 2 R ∧
      ∃ ρ : R →* Q, Function.Surjective ρ ∧
        ∀ r : R, (ρ r : F) = π (r : Y) := by
  let S : Sylow 2 Y := default
  have hQle : Q ≤ (S : Subgroup Y).map π := by
    simpa only [Sylow.coe_mapSurjective] using
      hQ.le_sylow_of_normal (S.mapSurjective hπ)
  let R : Subgroup Y := (S : Subgroup Y) ⊓ Q.comap π
  let ρ : R →* Q := (π.comp R.subtype).codRestrict Q (fun r => r.property.2)
  have hRp : IsPGroup 2 R := S.isPGroup'.of_injective
    (Subgroup.inclusion (show R ≤ (S : Subgroup Y) from inf_le_left))
    (Subgroup.inclusion_injective _)
  refine ⟨R, hRp, ρ, ?_, fun r => rfl⟩
  intro q
  obtain ⟨y, hyS, hy⟩ := Subgroup.mem_map.mp (hQle q.property)
  refine ⟨⟨y, hyS, ?_⟩, Subtype.ext hy⟩
  change π y ∈ Q
  rw [hy]
  exact q.property

theorem normal_elementary_binary_image_card_le_four [Finite Y]
    (hno : ∀ V : Subgroup Y, ¬ IsKleinFour V)
    (π : Y →* F) (hπ : Function.Surjective π)
    (Q : Subgroup F) [Q.Normal] [Finite Q] [IsElementaryAbelian 2 Q] :
    Nat.card Q ≤ 4 := by
  obtain ⟨R, hRp, ρ, hρ, _⟩ := normal_binary_image_has_actual_two_group_cover
    π hπ Q (IsElementaryAbelian.isPGroup 2 Q)
  exact elementary_binary_quotient_card_le_four
    (no_four_group_of_injective hno R.subtype R.subtype_injective) hRp ρ hρ

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair
