module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BLin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

theorem fzl59b :
    Fz59B := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau s u b T₃ h
  have hcent : 2 ^ 8 ≤ Nat.card ↥(T₃ ⊓ centralizer ({s} : Set G)) := by
    by_cases hs1 : s = 1
    · have hle : T₃ ≤ centralizer ({s} : Set G) := by
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        rw [Set.mem_singleton_iff] at hc
        rw [hc, hs1, one_mul, mul_one]
      rw [inf_eq_left.mpr hle, h.card_T₃]
      norm_num
    · exact (fzl59c_facts h).cent_B s (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)) hs1
  exact fzl59b_of_facts h hcent (fz59_linear h)

end CFSG.OddStandard.SmallF3.FritzII
