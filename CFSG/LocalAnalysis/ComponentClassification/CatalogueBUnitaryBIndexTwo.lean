module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalIndexTwoB

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryB

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem galoisField_unitaryFieldData (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    UnitaryFieldData p f (GaloisField p (2 * f)) :=
  ⟨Fact.out, hf, GaloisField.card p (2 * f) (by omega)⟩

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem odd_unitary_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (n p f : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hn : 3 ≤ n)
    (hmodel : Assembly.ComponentType.ClassicalModel (GeneralizedFitting.subgroup G) .PSU n p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  obtain ⟨⟨-, hf, -, -⟩, ⟨θ⟩⟩ := hmodel
  let h := galoisField_unitaryFieldData p f hf
  let psi : GeneralizedFitting.subgroup G ≃* unitaryPSU h n :=
    (θ.trans (ClassicalModelStatedBridge.psuModelEquiv n p f)).trans
      (unitaryPSUEquiv h (by omega : 1 ≤ n)).symm
  have : Finite (unitaryPSU h n) := Finite.of_equiv _ psi.toEquiv
  have hfixed : ∀ alpha : MulAut (unitaryPSU h n), alpha * alpha = 1 → alpha ≠ 1 →
      ∀ r : ℕ, r.Prime → ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha),
        CFSG.IsPComponent r L → CFSG.IsQuasisimple L :=
    fun alpha h2 h1 r hr L hL => odd_unitary_involution_fixed_p_components h hp hn alpha
      (orderOf_eq_prime (by rw [pow_two]; exact h2) h1) r hr L hL
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => CatalogueBOrthogonalIndexTwoB.local_bad_eq_bot_of_coordinate_model hnonab
      hindex psi hfixed hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

end CFSG.ComponentClassification.CatalogueBUnitaryB
