module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinBasic

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.ComponentClassification.GMS78.Finkelstein

namespace Finkelstein.Hyp

variable {U : Type} [Group U] {n : ℕ} {t y : MulAut U}

theorem psi_mul_of_comm (hc : ∀ a b : U, a * b = b * a) (u v : U) :
    psi t (u * v) = psi t u * psi t v := by
  unfold psi
  calc (u * v)⁻¹ * t (u * v) = v⁻¹ * (u⁻¹ * t u) * t v := by rw [map_mul]; group
    _ = (u⁻¹ * t u) * v⁻¹ * t v := by rw [hc v⁻¹ (u⁻¹ * t u)]
    _ = u⁻¹ * t u * (v⁻¹ * t v) := by group

@[expose] def psiHomOfComm (hc : ∀ a b : U, a * b = b * a) (t : MulAut U) : U →* U where
  toFun := psi t
  map_one' := psi_eq_one_iff.mpr (one_mem _)
  map_mul' := psi_mul_of_comm hc

variable [Finite U] (h : Finkelstein.Hyp U n t y)
include h

end Finkelstein.Hyp

end CFSG.SeitzReduction.RankOne
