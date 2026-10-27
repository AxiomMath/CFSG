module

public import CFSG.Certificates.Kernel.SlpRelSound
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.KS.SlpRel

variable {G : Type*} [Group G]

theorem slpG_append (p q : List (List ℕ)) (R : List G) :
    slpG (p ++ q) R = slpG q (slpG p R) := by
  unfold slpG
  rw [List.foldl_append]

theorem slpG_length : ∀ (p : List (List ℕ)) (R : List G),
    (slpG p R).length = R.length + p.length
  | [], R => rfl
  | w :: p, R => by
    have := slpG_length p (R ++ [(w.map fun l => R.getD (l - 1) 1).prod])
    change (slpG p _).length = _
    rw [this, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem slpG_getD_lt : ∀ (p : List (List ℕ)) (R : List G) {i : ℕ}, i < R.length →
    (slpG p R).getD i 1 = R.getD i 1
  | [], R, i, _ => rfl
  | w :: p, R, i, hi => by
    change (slpG p _).getD i 1 = _
    rw [slpG_getD_lt p _ (by rw [List.length_append]; omega), getD_push, if_pos hi]

theorem prod_mem_of_forall (H : Subgroup G) : ∀ l : List G, (∀ x ∈ l, x ∈ H) → l.prod ∈ H
  | [], _ => H.one_mem
  | x :: l, h => by
    rw [List.prod_cons]
    exact H.mul_mem (h x List.mem_cons_self)
      (prod_mem_of_forall H l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem slpG_mem (H : Subgroup G) (allowed : List ℕ) (base : ℕ) :
    ∀ (p : List (List ℕ)) (R : List G), (∀ w ∈ p, ∀ l ∈ w, l ∈ allowed ∨ base < l) →
      (∀ l, (l ∈ allowed ∨ base < l) → R.getD (l - 1) 1 ∈ H) →
      ∀ l, (l ∈ allowed ∨ base < l) → (slpG p R).getD (l - 1) 1 ∈ H
  | [], R, _, hR => hR
  | w :: p, R, hp, hR => by
    refine slpG_mem H allowed base p _ (fun w' hw' => hp w' (List.mem_cons_of_mem _ hw')) ?_
    intro l hl
    rw [getD_push]
    split_ifs
    · exact hR l hl
    · refine prod_mem_of_forall H _ fun x hx => ?_
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
      exact hR m (hp w List.mem_cons_self m hm)
    · exact H.one_mem

end CFSG.KS.SlpRel

end
