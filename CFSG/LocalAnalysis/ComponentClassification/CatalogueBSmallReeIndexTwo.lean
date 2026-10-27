module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalIndexTwoB
public import CFSG.LieType.Ree.SmallReeModelSchreier

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem small_Ree_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (p f : ℕ)
    (hmodel : ReeTitsModel (GeneralizedFitting.subgroup G) .twistedG2 p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  obtain ⟨-, -, hp, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := small_Ree_model_Schreier _ p f hmodel
  subst hp
  obtain ⟨-, a, hfa, hrel⟩ := hmodel
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨psi⟩ := hiso a K hfa hK ⟨e⟩
  have ha : 1 ≤ a := by omega
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := hfa ▸ hK
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => CatalogueBOrthogonalIndexTwoB.local_bad_eq_bot_of_coordinate_model hnonab
      hindex psi (fun α h2 h1 r hr L hL => small_Ree_involution_fixed_p_components a ha K hK' α
        (orderOf_eq_prime (by rw [pow_two]; exact h2) h1) r hr L hL) hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

end CFSG.ComponentClassification.CatalogueBSmallRee
