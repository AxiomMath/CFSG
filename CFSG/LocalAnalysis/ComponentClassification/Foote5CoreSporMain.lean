module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporA
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporA2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporB
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporC
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporD

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint

variable {K : Type} [Group K] [Finite K]

theorem coreCondition_of_sporadicRep
    (hON : ONanOuterCardLeTwo) {a : K} (ha : orderOf a = 2) {Y : Subgroup K}
    (hY : IsPComponent 2 Y) (hspor : NativeSporadic.SporadicRep (Y ⧸ Open.fusionZStar Y))
    (hHe : ¬ Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* NativeSporadic.He)) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K := by
  obtain ⟨s, ⟨θ⟩⟩ := hspor
  cases s with
  | M11 => exact coreCondition_M11 ha hY θ
  | M12 => exact coreCondition_M12 ha hY θ
  | M22 => exact coreCondition_M22 ha hY θ
  | M23 => exact coreCondition_M23 ha hY θ
  | M24 => exact coreCondition_M24 ha hY θ
  | J1 => exact coreCondition_J1 ha hY θ
  | J2 => exact coreCondition_J2 ha hY θ
  | J3 => exact coreCondition_J3 ha hY θ
  | J4 => exact coreCondition_J4 ha hY θ
  | Co1 => exact coreCondition_Co1 ha hY θ
  | Co2 => exact coreCondition_Co2 ha hY θ
  | Co3 => exact coreCondition_Co3 ha hY θ
  | Fi22 => exact coreCondition_Fi22 ha hY θ
  | Fi23 => exact coreCondition_Fi23 ha hY θ
  | Fi24Prime => exact coreCondition_Fi24Prime ha hY θ
  | HS => exact coreCondition_HS ha hY θ
  | McL => exact coreCondition_McL ha hY θ
  | He => exact (hHe ⟨θ⟩).elim
  | Ru => exact coreCondition_Ru ha hY θ
  | Suz => exact coreCondition_Suz ha hY θ
  | ONan => exact coreCondition_ONan hON ha hY θ
  | HN => exact coreCondition_HN ha hY θ
  | Ly => exact coreCondition_Ly ha hY θ
  | Th => exact coreCondition_Th ha hY θ
  | B => exact coreCondition_B ha hY θ
  | M => exact coreCondition_M ha hY θ

end CFSG.ComponentClassification.Foote5
