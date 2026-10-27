module

public import CFSG.ClassicalInvolution.Q3.Q3NSModel
public import CFSG.Assembly.RankThreeEvenDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.BSC CFSG.ClassicalInvolution.Q3.Q3NS
  CFSG.ClassicalInvolution.Q3.Q3W

section Model

theorem commFund_of_connected {t : StatedLieTag} {n : ℕ} {c : CompData}
    (hc : c = CompData.model t n) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hnA1 : ¬ (t = .PSL ∧ n = 2))
    (hconn : CommFamilyConnected c.fund) : ∀ R ∈ c.fund, ∃ S ∈ c.fund, Commutes R S := by
  have hsc := singleClass_of_eq_model hc hfund hadm hG2 hD4
  subst hc
  intro R₁ hR₁
  obtain ⟨R, hR, S, hS, hRS, -⟩ := exists_commuting_pair_ne3 hfund hadm hG2 hD4 hnA1 hconn hR₁
  obtain ⟨g, hg⟩ := hsc R hR R₁ hR₁
  refine ⟨conjSub g S, conjSub_mem_modelFund hS g, ?_⟩
  rw [hg]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [hRS a ha b hb]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

end Model

end CFSG.ClassicalInvolution.Q3.Q3PP
