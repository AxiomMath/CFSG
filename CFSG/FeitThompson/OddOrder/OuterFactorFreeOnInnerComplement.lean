module

public import Mathlib.GroupTheory.Complement

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {M : Type*} [Group M] {J B H U : Subgroup M}

theorem inf_centralizer_eq_bot_of_inf_centralizer_le
    [J.Normal] [(H.subgroupOf J).Normal]
    (_hJB : J.IsComplement' B) (hsup : H ⊔ U = J) (hdisj : Disjoint H U)
    (_hBU : B ≤ normalizer (U : Set M))
    (hCJ : ∀ b ∈ B, b ≠ 1 → J ⊓ centralizer {b} ≤ H) :
    ∀ b ∈ B, b ≠ 1 → U ⊓ centralizer {b} = ⊥ := by
  have hUJ : U ≤ J := hsup ▸ le_sup_right
  intro b hb hb1
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxC⟩
  exact mem_bot.mpr (Subgroup.disjoint_def.mp hdisj (hCJ b hb hb1 ⟨hUJ hxU, hxC⟩) hxU)

theorem not_commute_of_mem_of_ne_one
    [J.Normal] [(H.subgroupOf J).Normal]
    (hJB : J.IsComplement' B) (hsup : H ⊔ U = J) (hdisj : Disjoint H U)
    (hBU : B ≤ normalizer (U : Set M))
    (hCJ : ∀ b ∈ B, b ≠ 1 → J ⊓ centralizer {b} ≤ H)
    {b : M} (hb : b ∈ B) (hb1 : b ≠ 1) {x : M} (hx : x ∈ U) (hx1 : x ≠ 1) :
    ¬ Commute x b := by
  intro hcomm
  refine hx1 (mem_bot.mp ?_)
  rw [← inf_centralizer_eq_bot_of_inf_centralizer_le hJB hsup hdisj hBU hCJ b hb hb1]
  exact ⟨hx, mem_centralizer_singleton_iff.mpr hcomm⟩

end

end CFSG.FeitThompson
