module

public import CFSG.ClassicalInvolution.Q3.Q3YSInputs
public import CFSG.ClassicalInvolution.Q3.Q3YModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank


theorem modelFourGroup3On_centerless : ModelFourGroup3On fun t =>
    t = .G2 ∨ t = .F4 ∨ t = .E8 ∨ t = .trialityD4 ∨ t = .twistedE6 := by
  intro t n ht hfund hadm _ heven
  have hcen : Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K = ⊥ :=
    Q3Y.center_modelUniv_eq_bot_of_tag ht hadm
  have hfin : Finite (modelUniv t n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three hfund hadm
  have hq : CFSG.Open.IsQuasisimple (modelUniv t n 3 1 Nat.prime_three).K :=
    ModelFacts.isQuasisimple_modelUniv t n 3 1 Nat.prime_three hfund hadm
  have hs := Q3Y.isSimpleGroup_of_center_eq_bot hq hcen
  obtain ⟨E, hE, hEcard⟩ := Q3Y.exists_fourGroup_of_two_le_twoRank
    (CFSG.Walter.two_le_twoRank _ (Q3Y.exists_noncomm_of_isQuasisimple hq) heven)
  exact ⟨E, hE, hEcard, by rw [hcen]; exact inf_bot_eq E⟩

end CFSG.ClassicalInvolution.Q3.Q3YS
