module

public import CFSG.Holt.SL6.Defs
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource

public section

namespace CFSG.Holt.SL6

open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.SymmetricLocal

theorem exists_sylow_central_stdTransvection :
    ∃ P : Sylow 2 SL(6, ZMod 2), stdTransvection ∈ (P : Subgroup SL(6, ZMod 2)) ∧
      ∀ s ∈ (P : Subgroup SL(6, ZMod 2)), s * stdTransvection = stdTransvection * s := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 6) (by norm_num)
  have hc := utTransvection_corner_mem_center (n := 6) (K := ZMod 2) (by norm_num) 1
  have hz : ((utTransvection (corner_lt (by norm_num : 2 ≤ 6)) (1 : ZMod 2) :
      unitriangular 6 (ZMod 2)) : SL(6, ZMod 2)) = stdTransvection := rfl
  refine ⟨P, ?_, ?_⟩
  · rw [hP, ← hz]
    exact Subtype.mem _
  · intro s hs
    rw [hP] at hs
    rw [← hz]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨s, hs⟩)

end CFSG.Holt.SL6
