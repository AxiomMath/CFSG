module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieTwoClassical
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieTwoExc

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

theorem lieTwo_eq_psl_three_two {t : StatedLieTag} {m f e h : ℕ}
    (hadm : StatedLieAdmissible t m 2 f)
    (hcof : lieOrderCofactor t m (2 ^ f) = h * lieOrderDivisor t m (2 ^ f))
    (he : e = lieSylowExponent t m * f) (hdiv : h ∣ (2 ^ e - 1) * e) :
    t = .PSL ∧ m = 3 ∧ f = 1 := by
  obtain ⟨-, hf, hc⟩ := hadm
  cases t with
  | PSL =>
    obtain ⟨hm, -, -⟩ := hc
    exact ⟨rfl, LieTwo.psl hm hf hcof he hdiv⟩
  | PSU => exact (LieTwo.psu hc.1 hf hcof he hdiv).elim
  | PSp => exact (LieTwo.psp hc.1 hf hcof he hdiv).elim
  | POmegaOdd => exact absurd rfl hc.2
  | POmegaPlus => exact (LieTwo.omegaPlus hc hf hcof he hdiv).elim
  | POmegaMinus => exact (LieTwo.omegaMinus hc hf hcof he hdiv).elim
  | G2 =>
    have hf2 : 2 ≤ f := by
      by_contra hf2
      obtain rfl : f = 1 := by omega
      exact absurd hc.2 (by norm_num)
    exact (LieTwo.g2 hf2 hcof he hdiv).elim
  | F4 => exact (LieTwo.f4 hf hcof he hdiv).elim
  | E6 => exact (LieTwo.e6 hf hcof he hdiv).elim
  | E7 => exact (LieTwo.e7 hf hcof he hdiv).elim
  | E8 => exact (LieTwo.e8 hf hcof he hdiv).elim
  | twistedE6 => exact (LieTwo.twistedE6 hf hcof he hdiv).elim
  | trialityD4 => exact (LieTwo.trialityD4 hf hcof he hdiv).elim
  | twistedB2 => exact (LieTwo.twistedB2 hf hcof he hdiv).elim
  | twistedG2 => exact absurd hc.2.1 (by norm_num)
  | twistedF4 => exact (LieTwo.twistedF4 hf hcof he hdiv).elim
  | Tits =>
    obtain ⟨-, -, rfl⟩ := hc
    exact (LieTwo.tits hcof he hdiv).elim

theorem hallTwoArith_lie_two {t : StatedLieTag} {m f e h : ℕ}
    (hadm : StatedLieAdmissible t m 2 f)
    (hcof : lieOrderCofactor t m (2 ^ f) = h * lieOrderDivisor t m (2 ^ f))
    (he : e = lieSylowExponent t m * f) (_he1 : 1 ≤ e) (_hh : Odd h)
    (hdiv : h ∣ (2 ^ e - 1) * e) :
    t = .PSL ∧ m = 3 ∧ f = 1 :=
  lieTwo_eq_psl_three_two hadm hcof he hdiv

end CFSG.SeitzReduction.RankOne
