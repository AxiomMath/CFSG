module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithAltSpor
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieTwo

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

theorem odd_lieOrderCofactor_two {t : StatedLieTag} {m f : ℕ}
    (hadm : StatedLieAdmissible t m 2 f) : Odd (lieOrderCofactor t m (2 ^ f)) :=
  Nat.coprime_two_right.1 (lieOrderCofactor_coprime hadm)

theorem odd_lieOrderDivisor_two {t : StatedLieTag} {m f : ℕ}
    (hadm : StatedLieAdmissible t m 2 f) : Odd (lieOrderDivisor t m (2 ^ f)) :=
  (odd_lieOrderCofactor_two hadm).of_dvd_nat (lieOrderDivisor_dvd_cofactor hadm)

theorem hallTwoArith_lie_two_of_mul_eq {t : StatedLieTag} {m f c : ℕ}
    (hadm : StatedLieAdmissible t m 2 f)
    (hc : c * lieOrderDivisor t m (2 ^ f) = lieOrderNumerator t m (2 ^ f))
    (H : HallTwoArith c) : t = .PSL ∧ m = 3 ∧ f = 1 := by
  obtain ⟨e, h, he1, rfl, hh, hdiv⟩ := H
  rw [lieOrderNumerator_eq hadm, ← pow_mul, mul_assoc] at hc
  obtain ⟨rfl, h2⟩ := two_pow_mul_odd_inj (hh.mul (odd_lieOrderDivisor_two hadm))
    (odd_lieOrderCofactor_two hadm) hc
  exact hallTwoArith_lie_two hadm h2.symm (mul_comm _ _) he1 hh hdiv

end CFSG.SeitzReduction.RankOne
