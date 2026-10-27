module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieG2F4E8
public import CFSG.LieType.Chevalley.OddE6AllInvolutionComponents
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents
public import CFSG.LieType.Chevalley.OddTrialityAllInvolutionComponents
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddLie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem odd_E6_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (p f : ℕ) (hp2 : p ≠ 2)
    (hmodel : ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) .E6 p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hmodel.2
  have hKodd := odd_card_of_card_eq_odd_prime_pow hmodel.1.1 hp2 hK
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => CatalogueBOrthogonalIndexTwoB.local_bad_eq_bot_of_coordinate_model hnonab
      hindex e (fun α h2 _ r hr L hL => odd_E6_all_involution_fixed_p_components K hKodd α
        (by rw [pow_two]; exact h2) r hr L hL) hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

theorem odd_E7_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (p f : ℕ) (hp2 : p ≠ 2)
    (hmodel : ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) .E7 p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hmodel.2
  have hKodd := odd_card_of_card_eq_odd_prime_pow hmodel.1.1 hp2 hK
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => CatalogueBOrthogonalIndexTwoB.local_bad_eq_bot_of_coordinate_model hnonab
      hindex e (fun α h2 _ r hr L hL =>
        LieType.AlgebraicGroups.odd_E7_all_involution_fixed_p_components K hKodd α
          (by rw [pow_two]; exact h2) r hr L hL) hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

theorem odd_triality_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (p f : ℕ) (hp2 : p ≠ 2)
    (hmodel : ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) .trialityD4 p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  have hp : p.Prime := hmodel.1.1
  have hf : 1 ≤ f := hmodel.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hmodel.2
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => CatalogueBOrthogonalIndexTwoB.local_bad_eq_bot_of_coordinate_model hnonab
      hindex e (fun α h2 _ r hr L hL => odd_triality_all_involution_fixed_p_components hp hp2 hf
        K hK σ hσ α (by rw [pow_two]; exact h2) r hr L hL) hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

end CFSG.ComponentClassification.CatalogueBOddLie
