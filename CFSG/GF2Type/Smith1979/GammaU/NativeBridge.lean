module

public import Certificates.Data.CFSGNative.GammaU.Core
public import CFSG.GF2Type.Smith1979.GammaU.StepCInputs
public import CFSG.GF2Type.Smith1979.GammaU.EnumDefs
public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairInputs

public section

namespace CFSG.GF2Type.Smith1979.GammaU

theorem native_q0b : @CFSG.GammaU.Native.q0b = @q0b := rfl

theorem native_appN : @CFSG.GammaU.Native.appN = @appN := rfl

theorem native_f0b : @CFSG.GammaU.Native.f0b = @f0b := rfl

theorem native_spanList : @CFSG.GammaU.Native.spanList = @spanList := by
  funext vs
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [CFSG.GammaU.Native.spanList, spanList, ih]

theorem native_bfsRound : @CFSG.GammaU.Native.bfsRound = @bfsRound := rfl

theorem native_bfsClosure : @CFSG.GammaU.Native.bfsClosure = @bfsClosure := by
  funext σ κ _ _ key fs fuel
  induction fuel with
  | zero => funext frontier seen visited; rfl
  | succ fuel ih =>
    funext frontier seen visited
    simp only [CFSG.GammaU.Native.bfsClosure, bfsClosure, ih, native_bfsRound]

namespace StepA

theorem native_a0 : @CFSG.GammaU.Native.a0 = @a0 := rfl

theorem native_d0 : @CFSG.GammaU.Native.d0 = @d0 := rfl

theorem native_idR : @CFSG.GammaU.Native.idR = @idR := rfl

theorem native_mulR : @CFSG.GammaU.Native.mulR = @mulR := rfl

theorem native_isoN : @CFSG.GammaU.Native.isoN = @isoN := rfl

theorem native_gammaUN : @CFSG.GammaU.Native.gammaUN = @gammaUN := rfl

theorem native_compOf : @CFSG.GammaU.Native.compOf = @compOf := rfl

theorem native_compGens : @CFSG.GammaU.Native.compGens = @ResPair.compGens := rfl

theorem native_orbitOf : @CFSG.GammaU.Native.orbitOf = @orbitOf := by
  unfold CFSG.GammaU.Native.orbitOf orbitOf
  simp only [native_bfsClosure, native_appN]

theorem native_closedCheck : @CFSG.GammaU.Native.closedCheck = @Enum.closedCheck := rfl

end StepA

end CFSG.GF2Type.Smith1979.GammaU
