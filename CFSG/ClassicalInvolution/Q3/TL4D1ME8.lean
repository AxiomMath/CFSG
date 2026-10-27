module

public import CFSG.ClassicalInvolution.Q3.TL3T16

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G]

structure E8Basis (E : Subgroup G) (e : Fin 3 → G) : Prop where
  sq : ∀ x ∈ E, x * x = 1
  card : Nat.card E = 8
  mem : ∀ k, e k ∈ E
  ne0 : e 0 ≠ 1
  ne1 : e 1 ≠ 1 ∧ e 1 ≠ e 0
  ne2 : e 2 ≠ 1 ∧ e 2 ≠ e 0 ∧ e 2 ≠ e 1 ∧ e 2 ≠ e 0 * e 1

theorem exists_mem_not_mem [Finite G] {E : Subgroup G} (S : Finset G)
    (hS : S.card < Nat.card E) : ∃ x ∈ E, x ∉ S := by
  classical
  by_contra h
  push Not at h
  have hle : Nat.card E ≤ S.card := by
    have := Set.ncard_le_ncard (fun x hx => h x hx : (E : Set G) ⊆ (S : Set G))
      (Finset.finite_toSet S)
    rwa [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at this
  omega

theorem exists_e8Basis [Finite G] {E : Subgroup G} (hsq : ∀ x ∈ E, x * x = 1)
    (hc : Nat.card E = 8) : ∃ e : Fin 3 → G, E8Basis E e := by
  classical
  obtain ⟨a, ha, ha1⟩ := exists_mem_not_mem (E := E) {1} (by rw [hc]; simp)
  obtain ⟨b, hb, hb1⟩ := exists_mem_not_mem (E := E) {1, a} (by
    rw [hc]; exact lt_of_le_of_lt (Finset.card_le_two) (by norm_num))
  obtain ⟨c, hc', hc1⟩ := exists_mem_not_mem (E := E) {1, a, b, a * b} (by
    rw [hc]; exact lt_of_le_of_lt (Finset.card_le_four) (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 hb1 hc1
  refine ⟨![a, b, c], hsq, hc, fun k => ?_, ha1, hb1, hc1⟩
  fin_cases k
  · exact ha
  · exact hb
  · exact hc'

@[expose] def e8Coord (e : Fin 3 → G) (v : Fin 3 → ZMod 2) : G :=
  e 0 ^ (v 0).val * e 1 ^ (v 1).val * e 2 ^ (v 2).val

variable {E : Subgroup G} {e : Fin 3 → G}

theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem pow_val_add (he : E8Basis E e) (k : Fin 3) (a b : ZMod 2) :
    e k ^ (a + b).val = e k ^ a.val * e k ^ b.val := by
  have h2 := he.sq _ (he.mem k)
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 + 1 : ZMod 2) = 0 by decide, ZMod.val_zero, pow_zero, ZMod.val_one, pow_one, h2]

theorem e8Coord_mem (he : E8Basis E e) (v : Fin 3 → ZMod 2) : e8Coord e v ∈ E :=
  E.mul_mem (E.mul_mem (E.pow_mem (he.mem 0) _) (E.pow_mem (he.mem 1) _)) (E.pow_mem (he.mem 2) _)

theorem e8Coord_add (he : E8Basis E e) (u v : Fin 3 → ZMod 2) :
    e8Coord e (u + v) = e8Coord e u * e8Coord e v := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => comm_of_sq he.sq hx hy
  have m := fun k (a : ZMod 2) => E.pow_mem (he.mem k) a.val
  unfold e8Coord
  simp only [Pi.add_apply]
  rw [pow_val_add he, pow_val_add he, pow_val_add he]
  set a0 := e 0 ^ (u 0).val
  set a1 := e 1 ^ (u 1).val
  set a2 := e 2 ^ (u 2).val
  set b0 := e 0 ^ (v 0).val
  set b1 := e 1 ^ (v 1).val
  set b2 := e 2 ^ (v 2).val
  have h1 : b0 * a1 = a1 * b0 := hcomm _ (m 0 _) _ (m 1 _)
  have h2 : b0 * a2 = a2 * b0 := hcomm _ (m 0 _) _ (m 2 _)
  have h3 : b1 * a2 = a2 * b1 := hcomm _ (m 1 _) _ (m 2 _)
  calc a0 * b0 * (a1 * b1) * (a2 * b2) = a0 * (b0 * a1) * b1 * a2 * b2 := by group
    _ = a0 * (a1 * b0) * b1 * a2 * b2 := by rw [h1]
    _ = a0 * a1 * b0 * (b1 * a2) * b2 := by group
    _ = a0 * a1 * b0 * (a2 * b1) * b2 := by rw [h3]
    _ = a0 * a1 * (b0 * a2) * b1 * b2 := by group
    _ = a0 * a1 * (a2 * b0) * b1 * b2 := by rw [h2]
    _ = a0 * a1 * a2 * (b0 * b1 * b2) := by group

theorem e8Coord_zero : e8Coord e 0 = 1 := by
  simp [e8Coord]

end CFSG.ClassicalInvolution.Q3.TL4
