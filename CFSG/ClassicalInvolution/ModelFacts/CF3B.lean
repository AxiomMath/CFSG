module

public import CFSG.ClassicalInvolution.ModelFacts.CF3A
public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3CII (eq_three_of_pow_eq_three ne_two_of_pow_eq_three)
open scoped MatrixGroups commutatorElement

theorem eq_one_of_sq_eq_one_of_pow_three {K : Type*} [Group K] {x : K} (h2 : x * x = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  calc x = (x * x) * x := by rw [h2, one_mul]
    _ = x ^ 3 := by rw [pow_succ, pow_two]
    _ = 1 := h3



section Fundamental

variable {p e : ℕ} [Fact p.Prime] {t : StatedLieTag} {n : ℕ}

theorem gen3_of_mem_longestFundamental3 (h3 : p ^ e = 3) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D) : Gen3 R := by
  have hp2 := ne_two_of_pow_eq_three h3
  obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4
    (longestFundamental_subset t _ hR)
  obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
  exact gen3_of_equiv_sl2 φ

end Fundamental

end CFSG.ClassicalInvolution.ModelFacts
