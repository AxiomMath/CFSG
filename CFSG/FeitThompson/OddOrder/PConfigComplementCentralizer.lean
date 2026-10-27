module

public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {M E W₁ W₂ : Subgroup G}

namespace IsWitnessedPConfiguration

theorem le_centralizer_W₁ (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    W₂ ≤ centralizer (W₁ : Set G) := fun _x hx =>
  mem_centralizer_iff.2 fun _y hy => (hc.commute_W₁_W₂ hy hx).eq

theorem inf_centralizer_W₁_eq_W₂ (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    (⁅M, M⁆ : Subgroup G) ⊓ centralizer (W₁ : Set G) = W₂ := by
  obtain ⟨w, hw, _, hcw⟩ := hc.exists_inf_centralizer_eq_W₂
  refine le_antisymm ?_
    (le_inf (hc.le_hallCore_W₂.trans hc.hallCore_le_commutator) hc.le_centralizer_W₁)
  calc (⁅M, M⁆ : Subgroup G) ⊓ centralizer (W₁ : Set G)
      ≤ (⁅M, M⁆ : Subgroup G) ⊓ centralizer {w} :=
        inf_le_inf_left _ (centralizer_le (by simpa using hw))
    _ = W₂ := hcw

theorem mem_W₂_iff_of_mem_commutator (hc : IsWitnessedPConfiguration M E W₁ W₂) {x : G}
    (hx : x ∈ (⁅M, M⁆ : Subgroup G)) :
    x ∈ W₂ ↔ ∀ w ∈ W₁, w * x = x * w := by
  rw [← hc.inf_centralizer_W₁_eq_W₂, mem_inf]
  simp [hx, mem_centralizer_iff]

end IsWitnessedPConfiguration

theorem IsPConfigurationIIToIV.inf_centralizer_W₁_eq_W₂
    (hc : IsPConfigurationIIToIV M E W₁ W₂) :
    (⁅M, M⁆ : Subgroup G) ⊓ centralizer (W₁ : Set G) = W₂ :=
  hc.isWitnessedPConfiguration.inf_centralizer_W₁_eq_W₂

end

end CFSG.FeitThompson
