module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Plus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Minus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint

theorem cl24_weak_index_bound (S : Type) [Group S] [Finite S] (H : Subgroup S) (hH : H ≠ ⊤) :
    (LieModel S .POmegaPlus 4 3 1 → 36 ≤ H.index) ∧
      (LieModel S .POmegaMinus 4 3 1 → 72 ≤ H.index) :=
  ⟨fun h => (cl24_index_plus h H hH).trans' (by norm_num),
    fun h => (cl24_index_minus h H hH).trans' (by norm_num)⟩

theorem a2l_cl4_weak_holds : HypA2.OmegaEightMinIndexWeak :=
  fun S _ _ H hH => cl24_weak_index_bound S H hH

end CFSG.OddStandard.SmallF3.HypA2Leaves
