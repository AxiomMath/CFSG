module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

section Steps

theorem kPerp_datum {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} (h : PerpHypS n Y R S t) {K : Subgroup Y}
    (hK : K ∈ CoreAssembly.conjClass (tightCore R)) (hz : IsUniqueInvolution K t) :
    KPerp (CoreAssembly.conjClass (tightCore R)) K =
      twinSet (CoreAssembly.conjClass (tightCore R)) K := by
  have hC := CoreData.of_S h.core
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hKt : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := ⟨hK, t, hU, hz⟩
  have e1 := A7T22.kPerp_eq_of_twin hC.hyp (CoreAssembly.mem_conjClass_self _) hKt
  have e2 : twinSet (CoreAssembly.conjClass (tightCore R)) K =
      twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    ext J
    constructor
    · rintro ⟨hJ, z, hzK, hzJ⟩
      exact ⟨hJ, z, (hzK.eq hz) ▸ hU, hzJ⟩
    · rintro ⟨hJ, z, hzK, hzJ⟩
      exact ⟨hJ, z, (hzK.eq hU) ▸ hz, hzJ⟩
  rw [e1, e2]
  exact h.perp

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
