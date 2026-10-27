module

public import CFSG.ClassicalInvolution.Q3.Q3TJRest
public import CFSG.ClassicalInvolution.Q3.Q3TJOrth

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

@[expose] def SteinbergOddAut3PSU : Prop :=
  ∀ n : ℕ, CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU n 3 1 →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → Subgroup.center X = ⊥ →
      ∀ f : (Generic.modelUniv .PSU n 3 1 Nat.prime_three).K →* X, Function.Surjective f →
        f.ker ≤ Subgroup.center (Generic.modelUniv .PSU n 3 1 Nat.prime_three).K →
          ∀ α : MulAut X, Odd (orderOf α) → ∃ g : X, α = MulAut.conj g

theorem steinbergOddAut3Rest_of_PSU (h : SteinbergOddAut3PSU) : SteinbergOddAut3Rest := by
  intro t n ht hadm X _ _ hX hZ f hf hker α hodd
  rcases ht with rfl | rfl | ⟨rfl, hn4⟩ | rfl
  · exact h n hadm X hX hZ f hf hker α hodd
  · exact exists_eq_conj_POmegaOdd hadm hZ f hf hker α hodd
  · exact exists_eq_conj_POmegaPlus hn4 hadm hZ f hf hker α hodd
  · exact exists_eq_conj_POmegaMinus hadm hZ f hf hker α hodd

theorem steinbergOddAut3_of_PSU (h : SteinbergOddAut3PSU) : SteinbergOddAut3 :=
  steinbergOddAut3_of_rest (steinbergOddAut3Rest_of_PSU h)

theorem modelOddAutRigid_of_PSU (hSt : SteinbergOddAut3PSU) (hD4 : D4OddAutInner3)
    (h3D4 : TrialityD4OddAutInner3) : ModelOddAutRigid :=
  modelOddAutRigid_of (steinbergOddAut3_of_PSU hSt) hD4 h3D4

end CFSG.ClassicalInvolution.Q3.Q3T
