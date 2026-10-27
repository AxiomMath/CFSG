module

public import CFSG.ClassicalInvolution.Asc77.AscT7TStar2
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25W

section Elementary

variable {G : Type} [Group G] [Finite G]

theorem not_mem_zStarOf_of_mem_badSub {F : Subgroup G} {z x : G} (hxF : x ∈ F)
    (hzF : ∀ y ∈ F, y * z = z * y)
    (hbad : z ∉ zStarOf (Subgroup.centralizer (F : Set G))) :
    z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) := by
  intro hgood
  apply hbad
  refine T7T.mem_zStarOf_of_le ?_ hgood ?_
  · intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hy x hxF).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hzF y hy

end Elementary

end C25W

end CFSG.ClassicalInvolution.Asc77
