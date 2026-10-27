module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBMinus
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBEight

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank CFSG.LieType.Universal.Spin

theorem rowDB : RowDB := by
  constructor
  · intro K _ _ m p f hp hp2 hK h5 hm t htZ ht1 htn
    rcases Nat.lt_or_ge m 5 with h | h
    · obtain rfl : m = 4 := by omega
      exact DB.conclZ_eight hp hp2 hK h5 htZ ht1 htn
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
      exact DB.conclZ_plus (by omega) hp hp2 hK h5 htZ ht1 htn
  · intro K _ _ m p f b c hirr hp hp2 hK h5 hm t htZ ht1 htn
    have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
    have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
    rcases Nat.lt_or_ge m 5 with h | h
    · obtain rfl : m = 4 := by omega
      exact (DB.false_of_minus_four hirr h2 htZ ht1 htn).elim
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
      exact DB.conclZ_minus (by omega) hirr hp hp2 hK h5 htZ ht1 htn

end CFSG.ComponentClassification.HarrisLit.T1.P54
