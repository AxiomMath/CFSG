module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S6Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_kPerp_iff_normalizes_a7 (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ Ω) {z u : G} (hz : IsUniqueInvolution K z) (hu : IsUniqueInvolution L u) :
    L ∈ KPerp Ω K ↔ z ∈ Subgroup.normalizer (L : Set G) := by
  by_cases hLK : L = K
  · subst hLK
    exact ⟨fun _ => Subgroup.le_normalizer hz.mem, fun _ => Set.mem_insert _ _⟩
  · constructor
    · rintro (h | h)
      · exact absurd h hLK
      · exact (mem_omegaNbr_iff_normalizes_a7 hΩ hcl hK hL hLK hz hu).mp h
    · intro h
      exact Or.inr ((mem_omegaNbr_iff_normalizes_a7 hΩ hcl hK hL hLK hz hu).mpr h)

end Basic

end CFSG.ClassicalInvolution.Hat2A7S
