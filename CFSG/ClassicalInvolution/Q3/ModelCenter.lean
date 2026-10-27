module

public import CFSG.ClassicalInvolution.Q3.ModelCenterTriality
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
public import CFSG.ClassicalInvolution.Q3.ModelCenterExceptional

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Exceptional

theorem modelFiniteCenterTwoGroup3 : ModelFiniteCenterTwoGroup3 := by
  intro t n hp hFT hadm
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  refine ⟨ModelFacts.finite_modelUniv (by norm_num) hp hFT hadm, ?_⟩
  have hF1 : Nat.card (GaloisField 3 1) = 2 ^ 1 + 1 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hF2 : Nat.card (GaloisField 3 (2 * 1)) = 2 ^ 3 + 1 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  cases t with
  | PSL => exact (centerExp_model_PSL (by have := hadm.2.2.1; omega) hF1).isPGroup
  | PSp => exact (centerExp_model_PSp hF1).isPGroup
  | PSU => exact (centerExp_model_PSU le_rfl hadm.2.2.1 hadm.2.2.2 hF2).isPGroup
  | POmegaOdd => exact (centerExp_model_POmegaOdd hadm.2.2.1 hadm.2.2.2 hF1).isPGroup
  | POmegaPlus => exact (centerExp_model_POmegaPlus (by have := hadm.2.2; omega) hF1).isPGroup
  | POmegaMinus => exact (centerExp_model_POmegaMinus hadm.2.2 hF1).isPGroup
  | G2 => exact (centerExp_adjoint .G2 (GaloisField 3 1)).isPGroup
  | F4 => exact (centerExp_adjoint .F4 (GaloisField 3 1)).isPGroup
  | E6 => exact (centerExp_e6 (GaloisField 3 1) hF1).isPGroup
  | E7 => exact (centerExp_e7 (GaloisField 3 1) hF1).isPGroup
  | E8 => exact (centerExp_adjoint .E8 (GaloisField 3 1)).isPGroup
  | twistedE6 =>
    exact (centerExp_fixedGroup (frobQ 3 1) (frobQ_frobQ 3 1 le_rfl) hF2).isPGroup
  | trialityD4 => exact (centerExp_model_trialityD4 le_rfl).isPGroup
  | twistedB2 => exact hFT.elim
  | twistedG2 => exact hFT.elim
  | twistedF4 => exact hFT.elim
  | Tits => exact hFT.elim

end CFSG.ClassicalInvolution.Q3
