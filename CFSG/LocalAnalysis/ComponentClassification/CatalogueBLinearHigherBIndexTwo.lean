module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalIndexTwoB
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourWitnesses

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBLinearHigherB

open CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem odd_higher_linear_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (n p f : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hn : 3 ≤ n)
    (hmodel : Assembly.ComponentType.ClassicalModel (GeneralizedFitting.subgroup G) .PSL n p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  obtain ⟨-, ⟨θ⟩⟩ := hmodel
  let psi := θ.trans (LinearFieldFour.pslModelEquivProjectiveSL n p f)
  have : Finite (LinearFlag.projectiveSL n (GaloisField p f)) := Finite.of_equiv _ psi.toEquiv
  have hchar : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ :=
    fun S hne htwo => CatalogueBOrthogonalIndexTwoB.local_bad_eq_bot_of_coordinate_model hnonab
      hindex psi (fun alpha hsq halpha => odd_higher_linear_involution_fixed_p_components n
        (GaloisField p f) hchar hn alpha halpha (by rw [sq]; exact hsq)) hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

end CFSG.ComponentClassification.CatalogueBLinearHigherB
