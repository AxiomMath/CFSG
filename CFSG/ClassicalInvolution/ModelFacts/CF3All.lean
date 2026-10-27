module

public import CFSG.ClassicalInvolution.ModelFacts.CF3Sp
public import CFSG.ClassicalInvolution.ModelFacts.CF3SpinPlus
public import CFSG.ClassicalInvolution.ModelFacts.CF3SpinOdd
public import CFSG.ClassicalInvolution.ModelFacts.CF3SpinMinus
public import CFSG.ClassicalInvolution.ModelFacts.CF3Exc
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalUnitary
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairF4
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance.Bootstrap



theorem commutingFundamentalGeneration3_nonTwisted {t : StatedLieTag} {n : ℕ} (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hE6 : t ≠ .twistedE6) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) : CommutingFundamentalGeneration 3 t n 1 := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  cases t with
  | PSL => exact commutingFundamentalGeneration_psl hp2 hadm
  | PSU => exact commutingFundamentalGeneration_psu hp2 hadm
  | PSp => exact commutingFundamentalGeneration3_psp h3 hadm
  | POmegaOdd => exact commutingFundamentalGeneration3_pOmegaOdd h3 hadm
  | POmegaPlus => exact commutingFundamentalGeneration3_pOmegaPlus h3 hadm
  | POmegaMinus => exact commutingFundamentalGeneration3_pOmegaMinus h3 hadm
  | G2 => exact absurd rfl hG2
  | trialityD4 => exact absurd rfl hD4
  | twistedE6 => exact absurd rfl hE6
  | F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact commutingFundamentalGeneration_f4 hp2 hadm
      (pairFrame_exc (Or.inr (Or.inl rfl)) hp2 hadm)
  | E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact commutingFundamentalGeneration3_exc h3 (Or.inl rfl) hadm
      (pairFrame_exc (Or.inr (Or.inr (Or.inl rfl))) hp2 hadm)
  | E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact commutingFundamentalGeneration3_exc h3 (Or.inr (Or.inl rfl)) hadm
      (pairFrame_exc (Or.inr (Or.inr (Or.inr rfl))) hp2 hadm)
  | E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact commutingFundamentalGeneration3_exc h3 (Or.inr (Or.inr rfl)) hadm
      (pairFrame_exc (Or.inl rfl) hp2 hadm)
  | twistedB2 => exact hfund.elim
  | twistedG2 => exact hfund.elim
  | twistedF4 => exact hfund.elim
  | Tits => exact hfund.elim

end CFSG.ClassicalInvolution.ModelFacts
