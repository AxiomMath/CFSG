module

public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace CFSG.KC.JordanReach

open Equiv MulAction

variable {n : ℕ}

theorem exists_to01 {G : Subgroup (Perm (Fin (n + 2)))} (t s : Fin (n + 2) → Perm (Fin (n + 2)))
    (ht : ∀ q, t q ∈ G ∧ t q 0 = q) (hs : ∀ q, q ≠ 0 → s q ∈ G ∧ s q 0 = 0 ∧ s q 1 = q)
    {a b : Fin (n + 2)} (hab : a ≠ b) : ∃ g ∈ G, g a = 0 ∧ g b = 1 := by
  set x := (t a)⁻¹ with hx
  have hxa : x a = 0 := by
    rw [hx, Perm.inv_eq_iff_eq]
    exact (ht a).2.symm
  have hxb : x b ≠ 0 := by
    intro h
    apply hab
    exact x.injective (h.trans hxa.symm) |>.symm
  obtain ⟨hsG, hs0, hs1⟩ := hs (x b) hxb
  refine ⟨(s (x b))⁻¹ * x, G.mul_mem (G.inv_mem hsG) (G.inv_mem (ht a).1), ?_, ?_⟩
  · rw [Perm.mul_apply, hxa, Perm.inv_eq_iff_eq, hs0]
  · rw [Perm.mul_apply, Perm.inv_eq_iff_eq, hs1]

theorem alternatingGroup_le_of_reach {G : Subgroup (Perm (Fin (n + 2)))}
    (t s : Fin (n + 2) → Perm (Fin (n + 2))) (ht : ∀ q, t q ∈ G ∧ t q 0 = q)
    (hs : ∀ q, q ≠ 0 → s q ∈ G ∧ s q 0 = 0 ∧ s q 1 = q) {c : Perm (Fin (n + 2))} (hc : c ∈ G)
    (hc3 : c.IsThreeCycle) : alternatingGroup (Fin (n + 2)) ≤ G := by
  have h2 : IsMultiplyPretransitive ↥G (Fin (n + 2)) 2 := by
    rw [is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg, hga, hgb⟩ := exists_to01 t s ht hs hab
    obtain ⟨h, hh, hhc, hhd⟩ := exists_to01 t s ht hs hcd
    refine ⟨⟨h⁻¹ * g, G.mul_mem (G.inv_mem hh) hg⟩, ?_, ?_⟩
    · change (h⁻¹ * g) a = c
      rw [Perm.mul_apply, hga, Perm.inv_eq_iff_eq, hhc]
    · change (h⁻¹ * g) b = d
      rw [Perm.mul_apply, hgb, Perm.inv_eq_iff_eq, hhd]
  exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (isPreprimitive_of_is_two_pretransitive h2) hc3 hc

end CFSG.KC.JordanReach

end
