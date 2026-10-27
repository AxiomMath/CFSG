module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf13Star

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open scoped commutatorElement

section Fused



variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {a₁ a₂ a₃ a₄ : Y}

theorem hyp51At_fused_of_cent (hP : PerpHypS n Y R S t)
    (F : StarFrame (CoreAssembly.conjClass (tightCore R)) t K K' K₃ K₄ a₁ a₂ a₃ a₄) {y : Y}
    (hy : y * t * y⁻¹ = a₁ * a₂ * a₃ * a₄) (hyc : y ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y)) :
    Hyp51At (Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y)) (a₁ * a₂ * (a₃ * a₄)) := by
  have hΩ := F.hyp
  have hsolv := hsolv_conjClass hP
  have hpy : y * (a₁ * a₂) = (a₁ * a₂) * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
  have hcc : a₁ * a₂ * (a₃ * a₄) = y * t * y⁻¹ := by rw [hy]; group
  have hpB : a₁ * a₂ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have hqB : a₃ * a₄ ∈ Subgroup.closure ({a₁ * a₂, t, a₃ * a₄} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have hxy : (y * a₁ * y⁻¹) * (y * a₂ * y⁻¹) = a₁ * a₂ := by
    have : (y * a₁ * y⁻¹) * (y * a₂ * y⁻¹) = y * (a₁ * a₂) * y⁻¹ := by group
    rw [this, hpy]; group
  rw [hcc]
  refine hyp51At_of_twin_pair hΩ hsolv (hΩ.conjInvariant y K F.hK) (hΩ.conjInvariant y K' F.hK')
    (F.hzK.conj y) (F.hzK'.conj y) (conj_mem_conjSub F.h₁) (conj_mem_conjSub F.h₂) F.isElemAbelian
    ?_ ?_ ?_ ?_ ?_
  · rw [← hcc]; exact Subgroup.mul_mem _ hpB hqB
  · rw [hxy]; exact hpB
  · intro h
    apply F.t1
    rw [← hy]
    calc y * t * y⁻¹ = (y * t * y⁻¹) := rfl
      _ = 1 := h
  · rw [hxy]; exact F.p_ne_one
  · rw [hxy, ← hcc]
    intro h
    apply F.q_ne_one
    have h' : (a₁ * a₂) * (a₃ * a₄) = (a₁ * a₂) * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h'

end Fused

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
