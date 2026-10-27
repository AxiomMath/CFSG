module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1AutCentralizerN0Proved

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem co1AutCentralizerA4_proved
    (hmult : OddMultTrivial .Co1) : Co1AutCentralizerA4 := by
  intro H _ _ L K u hcov hQ
  obtain ⟨N₀, hcan⟩ := exists_canLoc K (by rw [hQ.2.2.2.2.2]; decide)
  obtain ⟨h1, -, h3⟩ := co1AutCentralizerN0_proved hmult H L K u N₀ hcov hQ hcan
  have hle : autCentralizer L K ≤ autCentralizer L N₀ := fun α hα k hk => hα k (hcan.le hk)
  exact ⟨Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle),
    ElemBound.of_injective h3 (Subgroup.inclusion_injective hle)⟩

end CFSG.EvenSporadicStandard.Induction
