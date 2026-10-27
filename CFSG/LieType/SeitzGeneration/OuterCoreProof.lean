module

public import CFSG.LieType.SeitzGeneration.OuterSeed
public import CFSG.LieType.SeitzGeneration.UnitaryPhanShift
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreProof

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LocalAnalysis.ComponentInitial

theorem unitaryOuterHeisCore_of_finite_cases (h5 : OuterB12AtCard 5)
    (h8 : OuterB12AtCard 8) (h11 : OuterB12AtCard 11) : UnitaryOuterHeisCore := by
  intro ℓ f K _ h hq3 hq ω α hω hαN hnc
  have hf := h.one_le
  have hpow : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by omega : f ≠ 0) h.prime.one_lt
    omega
  have h14 := pow_ne_fourteen h.prime hf
  have hcases : ℓ ^ f = 5 ∨ ℓ ^ f = 8 ∨ ℓ ^ f = 11 ∨ 17 ≤ ℓ ^ f := by omega
  have hB : heisB12 ℓ f K ≤ outerHeisClosure ℓ f K ω α := by
    rcases hcases with h5' | h8' | h11' | h17
    · exact h5 ℓ f K h h5' ω α hω hαN hnc
    · exact h8 ℓ f K h h8' ω α hω hαN hnc
    · exact h11 ℓ f K h h11' ω α hω hαN hnc
    · exact heisB12_le_outerHeisClosure_of_large h hq3 h17 hω hαN hnc
  obtain ⟨s, hs, hsc⟩ := exists_shift_mem_outerHeisClosure h hω.pow_eq_one α
  exact eq_top_of_shift_of_heisB12_le h hq hs hsc hB

end CFSG.LieType.SeitzGeneration
