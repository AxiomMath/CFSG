module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank

public section

namespace CFSG

open Matrix
open CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {F : Type} [Field F]

theorem diagTorus_le_upperTriangular : diagTorus n F ≤ LinearFlag.upperTriangular n F := by
  intro D hD
  obtain ⟨d, -, hDmat⟩ := mem_diagTorus_iff.mp hD
  rw [LinearFlag.mem_upperTriangular]
  intro i j hij
  rw [hDmat, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]

theorem diagTorus_le_normalizer_unitriangular :
    diagTorus n F ≤ Subgroup.normalizer (LinearFlag.unitriangular n F : Set (SpecialLinearGroup (Fin n) F)) := by
  rw [Subgroup.le_set_normalizer_iff]
  intro D hD u hu
  exact LinearFlag.conj_mem_unitriangular (diagTorus_le_upperTriangular hD) hu

end CFSG
