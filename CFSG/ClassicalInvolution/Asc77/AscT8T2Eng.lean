module

public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T8T

variable {G : Type} [Group G] [Finite G]

theorem le_trivialOnQuotE {M : Fin 3 → Subgroup G} {x : Fin 3 → G} (i : Fin 3)
    (hX : ∀ j : Fin 3, x j ∈ trivialOnQuot (M i)) :
    Subgroup.closure ({x 0, x 1, x 2} : Set G) ≤ trivialOnQuot (M i) := by
  rw [Subgroup.closure_le]
  intro y hy
  have hj : ∃ j, y = x j := by
    rcases hy with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨j, rfl⟩ := hj
  exact hX j

end T8T

end CFSG.ClassicalInvolution.Asc77
