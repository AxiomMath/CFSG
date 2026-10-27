module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalIndexTwoB
public import CFSG.LieType.AlgebraicGroups.OddG2F4E8AllInvolutionComponents
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddLie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem odd_card_of_card_eq_odd_prime_pow {K : Type} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : Odd (Nat.card K) :=
  hK ▸ (hp.eq_two_or_odd'.resolve_left hp2).pow

theorem local_bad_eq_bot_of_odd_G2_F4_E8
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (e : GeneralizedFitting.subgroup G ≃* adjointGroup τ K)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    (S : Subgroup G) (hne : S ≠ ⊥) (htwo : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
  CatalogueBOrthogonalIndexTwoB.local_bad_eq_bot_of_coordinate_model hnonab hindex e
    (fun α h2 _ r hr L hL =>
      CFSG.LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components
        τ hτ K hK α (by rw [pow_two]; exact h2) r hr L hL) hproper S hne htwo

theorem odd_G2_F4_E8_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E8) (p f : ℕ) (hp2 : p ≠ 2)
    (hmodel : ChevalleyExceptionalModel (GeneralizedFitting.subgroup G) t p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  have hp : p.Prime := hmodel.1.1
  obtain ⟨τ, hτ, hm⟩ : ∃ τ : Tag, (τ = .G2 ∨ τ = .F4 ∨ τ = .E8) ∧
      UntwistedChevalleyModel (GeneralizedFitting.subgroup G) τ (p ^ f) := by
    rcases ht with rfl | rfl | rfl
    · exact ⟨.G2, Or.inl rfl, hmodel.2⟩
    · exact ⟨.F4, Or.inr (Or.inl rfl), hmodel.2⟩
    · exact ⟨.E8, Or.inr (Or.inr rfl), hmodel.2⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => local_bad_eq_bot_of_odd_G2_F4_E8 hnonab hindex τ hτ K
      (odd_card_of_card_eq_odd_prime_pow hp hp2 hK) e hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

end CFSG.ComponentClassification.CatalogueBOddLie
