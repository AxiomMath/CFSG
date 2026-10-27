module

public import CFSG.ClassicalInvolution.Balance.TheoremQNormalizer

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem isQuasisimple_of_deltaCore_eq_bot {C K F : Subgroup G} (hKC : IsSubnormal K C)
    (hKperf : commutator K = ⊤)
    (hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K))
    (hKF : K ≤ Subgroup.centralizer (F : Set G)) (hΔ : deltaCore F = ⊥)
    (hB : ∀ f ∈ F, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) K),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) K⁆ ≤ involutionOddCore f) :
    CFSG.Open.IsQuasisimple K := by
  have h1 := le_centralizer_oddCoreIn_inf_centralizer (C := C) (K := K) (E₀ := F) (L₀ := K)
    (F := F) hKC le_rfl le_rfl hKF hKperf hΔ hB
  refine isQuasisimple_of_oddCoreIn_le_centralizer hKperf hKq fun o ho => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hoF : o ∈ oddCoreIn K ⊓ Subgroup.centralizer (F : Set G) := ⟨ho, hKF (oddCoreIn_le K ho)⟩
  exact (Subgroup.mem_centralizer_iff.mp (h1 hk) o hoF).symm

end CFSG.ClassicalInvolution.Balance.Bootstrap
