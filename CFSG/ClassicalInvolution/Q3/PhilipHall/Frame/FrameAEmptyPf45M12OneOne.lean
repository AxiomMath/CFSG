module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Cfg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf46OneOne

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

theorem m12_20_1_1 {T : Type} [Group T] [Finite T] [CaseIAmbient T] {K : Subgroup T} {z : T}
    {J : Subgroup T} {zJ : T} {H S : Subgroup T} (cfg : M12Cfg K z J zJ H S) {n : T}
    (hn : n ∈ sigmaNorm K) {a : T} (ha : IsPGroup 2 (Subgroup.zpowers a)) (ha1 : a ≠ 1)
    (haN : a ∈ Subgroup.normalizer (conjSub n (firstFactor K) : Set T))
    (hac : ∀ x ∈ conjSub n (firstFactor K), a * x * a⁻¹ * x⁻¹ ∈ oddCoreOf (sigmaGen K)) :
    Subgroup.centralizer ({a} : Set T) ≤ sigmaNorm K :=
  cfg.toFrameCfg.cent_le_of_factor hn ha ha1 haN hac

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
