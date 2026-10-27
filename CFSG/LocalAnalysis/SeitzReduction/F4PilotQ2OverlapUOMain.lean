module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOOmegaParam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOBlock

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.LieType.BorelTits (unitaryInvolution)

@[expose] def TwoUnitary6CentInput : Prop :=
  ∀ (K F : Type) [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2],
    Nat.card K = 2 → Nat.card F = (2 ^ 1) ^ 2 → ∀ (ι : K →+* F)
      (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
      TwoSUCentValues .unitary6 (Nat.zero_le 1) ι hι

@[expose] def TwoUnitary7CentInput : Prop :=
  ∀ (K F : Type) [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2],
    Nat.card K = 2 → Nat.card F = (2 ^ 1) ^ 2 → ∀ (ι : K →+* F)
      (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
      TwoSUCentValues .unitary7 le_rfl ι hι

theorem twoUnitary6BlockValuesInput_of_cent (h : TwoUnitary6CentInput) :
    TwoUnitary6BlockValuesInput := fun K F _ _ _ _ _ hK hF ι hι =>
  twoUniBlockValues_unitary6 hF hι (h K F hK hF ι hι)

theorem twoUnitary7BlockValuesInput_of_cent (h : TwoUnitary7CentInput) :
    TwoUnitary7BlockValuesInput := fun K F _ _ _ _ _ hK hF ι hι =>
  twoUniBlockValues_unitary7 hF hι (h K F hK hF ι hι)

theorem twoOverlapInvUnitaryOmegaInput_of_cent (hU6 : TwoUnitary6CentInput)
    (hU7 : TwoUnitary7CentInput) (hPp : TwoOmegaPlusParamInput) (hVp : TwoOmegaPlusModelValues)
    (hPm : TwoOmegaMinusParamInput) (hVm : TwoOmegaMinusModelValues) :
    TwoOverlapInvUnitaryOmegaInput :=
  twoOverlapInvUnitaryOmegaInput_of_inputs (twoUnitary6BlockValuesInput_of_cent hU6)
    (twoUnitary7BlockValuesInput_of_cent hU7) hPp hVp hPm hVm

theorem twoOverlapInvUnitaryOmegaInput_of_values (hU6 : TwoUnitary6CentInput)
    (hU7 : TwoUnitary7CentInput) (hVp : TwoOmegaPlusModelValues)
    (hVm : TwoOmegaMinusModelValues) : TwoOverlapInvUnitaryOmegaInput :=
  twoOverlapInvUnitaryOmegaInput_of_cent hU6 hU7 twoOmegaPlusParamInput_holds hVp
    twoOmegaMinusParamInput_holds hVm

theorem twoOverlapInvGraphInput_of_values (hU6 : TwoUnitary6CentInput)
    (hU7 : TwoUnitary7CentInput) (hVp : TwoOmegaPlusModelValues)
    (hVm : TwoOmegaMinusModelValues) : TwoOverlapInvGraphInput :=
  twoOverlapInvGraphInput_of_unitaryOmega
    (twoOverlapInvUnitaryOmegaInput_of_values hU6 hU7 hVp hVm)

end CFSG.SeitzReduction.F4Pilot
