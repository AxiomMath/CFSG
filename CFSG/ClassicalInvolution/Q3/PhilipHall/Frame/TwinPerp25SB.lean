module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Defs

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank

theorem closure_az_pair {G : Type} [Group G] {a z : G} (hz2 : z * z = 1) :
    Subgroup.closure ({a * z, z} : Set G) = Subgroup.closure ({a, z} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · have h1 : a * z ∈ Subgroup.closure ({a * z, z} : Set G) := Subgroup.subset_closure (by simp)
      have h2 : z ∈ Subgroup.closure ({a * z, z} : Set G) := Subgroup.subset_closure (by simp)
      have h3 := Subgroup.mul_mem _ h1 h2
      have h4 : a * z * z = a := by rw [mul_assoc, hz2, mul_one]
      rw [h4] at h3
      rw [hx]
      exact h3
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.subset_closure (by simp)

theorem mul_z_z {G : Type} [Group G] {a z : G} (hz2 : z * z = 1) : a * z * z = a := by
  rw [mul_assoc, hz2, mul_one]

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R

