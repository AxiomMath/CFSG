module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5c3qma_exists_heavy {ζ w : Fin 6 → ZMod 2} (hζ : vecWeight ζ = 4)
    (hw : ¬ ∀ i j, ζ i = 1 → ζ j = 1 → w i = w j) :
    ∃ u ∈ [w, w + ζ, w + 1, w + 1 + ζ], u ≠ ζ ∧ (vecWeight u = 3 ∨ vecWeight u = 4) := by
  revert ζ w
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
