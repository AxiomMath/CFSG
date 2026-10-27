module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4GraphType
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientGraphField
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Field

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem twentySeven_dvd_fixedSubgroup_adjointD4 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (h3 : ¬ 3 ∣ ℓ)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.D4 K)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  have hℓ : ℓ.Prime := Fact.out
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hchar : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨g, a, σ, ε, hε, hαeq, -, hcase⟩ := outer_cube_normal_form_cases α hα3 hα
  rcases hcase with ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩
  · exact twentySeven_dvd_fixedSubgroup_D4_field hf K hK α hα3 hα
      (D4FieldType_of_normal_form hε0 hαeq)
  · exact twentySeven_dvd_card_fixedSubgroup_graphField K hK h3 α hα3 g a σ ε hε hε0 hσ1 hαeq
  · subst hσ1
    exact twentySeven_dvd_card_fixedSubgroup_graph K hK h3 α hα3 g a ε hε hε0 hαeq

end CFSG.HardMathSupport.Lang.E6Descent
