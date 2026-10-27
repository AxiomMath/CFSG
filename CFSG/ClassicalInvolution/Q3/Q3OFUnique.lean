module

public import CFSG.ClassicalInvolution.Q3.Q3WShape

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
open scoped MatrixGroups

section Kernel

variable {G : Type} [Group G] [Finite G]

theorem routeD3Setup_nonabelian {K : Subgroup G} {z : G} (hR : RouteD3Setup K z) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  apply hR.cls.not_le_center
  intro x _
  rw [Subgroup.mem_center_iff]
  intro g
  exact hcon g x

end Kernel

end CFSG.ClassicalInvolution.Q3.Q3OF
