module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore
public import CFSG.ClassicalInvolution.Q3.Q3NLCtx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement

section Nine

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem members_q8_of_isPGroup (h : PerpHypS n Y R S t)
    (h2 : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), Nonempty (↥J ≃* QuaternionGroup 2) := by
  have hC := CoreData.of_S h.core
  have hK₀q8 : Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) := by
    obtain ⟨P, hP, ⟨e⟩⟩ := hC.datum.exists_sylow_q8 hC.q8
    have hK2 := h2 _ (CoreAssembly.mem_conjClass_self _)
    have hPeq : tightCore R = P := hP.2.2 _ le_rfl hK2 hP.1
    rw [hPeq]
    exact ⟨e⟩
  rintro _ ⟨g, rfl⟩
  obtain ⟨e⟩ := hK₀q8
  exact ⟨(Subgroup.equivMapOfInjective (tightCore R) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩

end Nine

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
