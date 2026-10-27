module
public import Mathlib.GroupTheory.Subgroup.Simple

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

theorem normalizer_lt_top_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    {X : Subgroup G} (hbot : ⊥ < X) (htop : X < ⊤) :
    normalizer (X : Set G) < ⊤ := by
  refine lt_top_iff_ne_top.2 fun h => ?_
  rcases (normalizer_eq_top_iff.1 h).eq_bot_or_eq_top with hX | hX
  · exact hbot.ne' hX
  · exact htop.ne hX

theorem exists_conj_image_ne_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    {X : Subgroup G} (hbot : ⊥ < X) (htop : X < ⊤) :
    ∃ g : G, (fun x => g⁻¹ * x * g) '' (X : Set G) ≠ (X : Set G) := by
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (normalizer_lt_top_of_isSimpleGroup hbot htop)
  refine ⟨g⁻¹, fun h => hg ?_⟩
  rw [mem_normalizer_iff_conj_image_eq]
  simpa [MulAut.conj] using h

end CFSG.FeitThompson
