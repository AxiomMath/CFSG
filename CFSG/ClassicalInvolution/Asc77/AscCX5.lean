module

public import CFSG.ClassicalInvolution.Asc77.AscT7TZStar
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Gamma

variable {G : Type} [Group G] [Finite G]

theorem comm_of_mem_zStarOf {V : Subgroup G} (hV2 : IsPGroup 2 V) {z w y : G} (hzV : z ∈ V)
    (hyV : y ∈ V) (hgood : z ∈ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (hzw : z * w = w * z) (hyw : y * w = w * y) : y * z = z * y := by
  have hTV : Subgroup.closure ({y, z} : Set G) ≤ V := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hyV
    · exact hzV
  have hTC : Subgroup.closure ({y, z} : Set G) ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hyw
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzw
  have hzT : z ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
  have hyT : y ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (T7T.le_centralizer_of_mem_zStarOf hgood hzT hTC (hV2.to_le hTV) hyT)

end Gamma

end CFSG.ClassicalInvolution.Asc77.CX
