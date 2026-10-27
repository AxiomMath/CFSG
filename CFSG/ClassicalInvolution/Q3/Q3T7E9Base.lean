module

public import CFSG.ClassicalInvolution.Uniform.U8Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.RouteD.Exotic


theorem e189ModelAt_three_of_noTwinClass (t : StatedLieTag) (n : ℕ) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hno : ¬ ModelTwinClass 3 t n 1 2) : E189ModelAt 3 1 t n := by
  have hfund' : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
    cases t <;> trivial
  intro N _ F₁ hF₁ z₁ _ g _ _ h3 h4 h5
  exact absurd (modelTwinClass_two_of_swap t n 1 hfund' hadm hG2 hD4 hF₁ h3 h4 h5) hno

theorem e189ModelAt_three_psl_of_ne_four {n : ℕ} (hadm : StatedLieAdmissible .PSL n 3 1)
    (hn : n ≠ 4) : E189ModelAt 3 1 .PSL n := by
  have hn3 : 3 ≤ n := by
    have h1 := hadm.2.2.1
    have h2 : n ≠ 2 := fun hk => hadm.2.2.2.2 (by simp [hk])
    omega
  refine e189ModelAt_three_of_noTwinClass .PSL n (by simp [IsFundTag]) hadm (by decide)
    (by decide) fun h => hn ?_
  exact (modelTwinClass_psl (by norm_num) hn3 le_rfl h).1

theorem e189ModelAt_three_psu_of_ne_four {n : ℕ} (hadm : StatedLieAdmissible .PSU n 3 1)
    (hn : n ≠ 4) : E189ModelAt 3 1 .PSU n := by
  refine e189ModelAt_three_of_noTwinClass .PSU n (by simp [IsFundTag]) hadm (by decide)
    (by decide) fun h => hn ?_
  exact (modelTwinClass_psu (by norm_num) hadm le_rfl h).1

theorem e189ModelAt_three_psp_of_ne_two {n : ℕ} (hadm : StatedLieAdmissible .PSp n 3 1)
    (hn : n ≠ 2) : E189ModelAt 3 1 .PSp n := by
  refine e189ModelAt_three_of_noTwinClass .PSp n (by simp [IsFundTag]) hadm (by decide)
    (by decide) fun h => hn ?_
  exact (modelTwinClass_psp (by norm_num) hadm le_rfl h).1

theorem e189ModelAt_three_exc {t : StatedLieTag} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨
    t = .twistedE6) {n : ℕ} (hadm : StatedLieAdmissible t n 3 1) : E189ModelAt 3 1 t n := by
  have hfund : IsFundTag t := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [IsFundTag]
  have hG2 : t ≠ .G2 := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide
  exact e189ModelAt_three_of_noTwinClass t n hfund hadm hG2 hD4
    (CFSG.ClassicalInvolution.Uniform.noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (CFSG.ClassicalInvolution.Uniform.excLayer3 t n ht hadm) le_rfl)

end CFSG.ClassicalInvolution.Q3.Q3T7E9
