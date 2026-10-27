module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LieType.Chevalley.OddTwistedE6InnerInvolutionComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddLie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem odd_twisted_E6_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (p f : ℕ) (hp2 : p ≠ 2)
    (hmodel : ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) .twistedE6 p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  have hp : p.Prime := hmodel.1.1
  have hf : 1 ≤ f := hmodel.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf hmodel.2
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => CatalogueBOrthogonalIndexTwoB.local_bad_eq_bot_of_coordinate_model hnonab
      hindex e (fun α h2 _ r hr L hL => odd_twisted_E6_all_involution_fixed_p_components hp hf
        (hp.eq_two_or_odd'.resolve_left hp2).pow K hK σ hσ α (by rw [pow_two]; exact h2) r hr L
        hL) hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

theorem odd_E6_E7_twisted_E6_triality_B_frontier
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (t : StatedLieTag) (p f : ℕ)
    (ht : t = .E6 ∨ t = .E7 ∨ t = .twistedE6 ∨ t = .trialityD4) (hp2 : p ≠ 2)
    (hmodel : ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) t p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    CentralTwoBInclusion.Property G := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact (odd_E6_index_two_B_under_proper_subgroup_B hnonab hindex p f hp2 hmodel hproper).2
  · exact (odd_E7_index_two_B_under_proper_subgroup_B hnonab hindex p f hp2 hmodel hproper).2
  · exact (odd_twisted_E6_index_two_B_under_proper_subgroup_B hnonab hindex p f hp2 hmodel
      hproper).2
  · exact (odd_triality_index_two_B_under_proper_subgroup_B hnonab hindex p f hp2 hmodel
      hproper).2

end CFSG.ComponentClassification.CatalogueBOddLie
