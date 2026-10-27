module

public import CFSG.ClassicalInvolution.Q3.Q3NMComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups

theorem compFacts_of_valid (h0 : ModelClauseZero) (hM : M11Facts) {c : CompData}
    (hc : c.Valid) : CompFacts c := by
  rcases hc with ⟨t, n, ht, hadm, rfl⟩ | rfl | rfl
  · have hK := (h0 t n 3 1 Nat.prime_three ht hadm).1
    obtain ⟨hfin, hZ⟩ := modelFiniteCenterTwoGroup3 t n Nat.prime_three ht hadm
    have : Group.IsPerfect (CompData.model t n).G := ⟨hK.1⟩
    refine ⟨hfin, hZ, fun g hg => mem_center_of_commutator_mem le_rfl hg, ?_⟩
    intro M hMn h24
    have := hMn
    have := hfin
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hK M with hle | htop
    · exact absurd h24 (not_dvd_24_of_isPGroup (hZ.to_le hle))
    · exact htop
  · exact compFacts_sl23
  · exact compFacts_m11 hM

end CFSG.ClassicalInvolution.Q3.Q3NM
