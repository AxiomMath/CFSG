module

public import CFSG.GH74.GLS.IVK.A7.Core

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.A7Fin

open Equiv Equiv.Perm Subgroup MulAction CFSG.GH74.GLS.IVK.A7

section Jordan

theorem jordan7 (H : Subgroup (Perm (Fin 7))) (hT : ∀ j : Fin 7, ∃ h ∈ H, h 6 = j) {c : Perm (Fin 7)}
    (hc : c.IsThreeCycle) (hcH : c ∈ H) : alternatingGroup (Fin 7) ≤ H := by
  have hpt : IsPretransitive H (Fin 7) := ⟨fun x y => by
    obtain ⟨h₁, hh₁, e₁⟩ := hT x
    obtain ⟨h₂, hh₂, e₂⟩ := hT y
    refine ⟨⟨h₂ * h₁⁻¹, H.mul_mem hh₂ (H.inv_mem hh₁)⟩, ?_⟩
    show (h₂ * h₁⁻¹) x = y
    rw [← e₁, ← e₂]
    simp⟩
  have h7 : Nat.Prime (Nat.card (Fin 7)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hpp : IsPreprimitive H (Fin 7) := IsPreprimitive.of_prime_card h7
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hpp hc hcH

@[expose] def reachStep (L : List S7) (O : Finset (Fin 7)) : Finset (Fin 7) :=
  L.foldl (fun acc g => acc ∪ O.image (fun x => g x)) O

@[expose] def reach (L : List S7) : Finset (Fin 7) := (reachStep L)^[6] {6}

theorem mem_foldl_union {L : List S7} {O acc : Finset (Fin 7)} {j : Fin 7}
    (h : j ∈ L.foldl (fun acc g => acc ∪ O.image (fun x => g x)) acc) :
    j ∈ acc ∨ ∃ g ∈ L, ∃ x ∈ O, g x = j := by
  induction L generalizing acc with
  | nil => exact Or.inl h
  | cons g L ih =>
    rcases ih h with h1 | ⟨g', hg', x, hx, hxj⟩
    · rw [Finset.mem_union, Finset.mem_image] at h1
      rcases h1 with h1 | ⟨x, hx, hxj⟩
      · exact Or.inl h1
      · exact Or.inr ⟨g, List.mem_cons_self, x, hx, hxj⟩
    · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', x, hx, hxj⟩

theorem reach_sound {H : Subgroup S7} {L : List S7} (hL : ∀ g ∈ L, g ∈ H) :
    ∀ n : ℕ, ∀ j ∈ (reachStep L)^[n] ({6} : Finset (Fin 7)), ∃ h ∈ H, h 6 = j := by
  intro n
  induction n with
  | zero =>
    intro j hj
    simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at hj
    subst hj
    exact ⟨1, H.one_mem, rfl⟩
  | succ n ih =>
    intro j hj
    rw [Function.iterate_succ_apply'] at hj
    rcases mem_foldl_union (by simpa only [reachStep] using hj) with hj | ⟨g, hg, x, hx, rfl⟩
    · exact ih j hj
    · obtain ⟨h, hh, rfl⟩ := ih x hx
      exact ⟨g * h, H.mul_mem (hL g hg) hh, rfl⟩

end Jordan

section Table

@[expose] def V0list : List S7 := [1, r ^ 2, s * r, s * r ^ 3]

@[expose] def GCtab : List (S7 × List S7) :=
[
  (swap 4 5, [swap 0 1 * swap 1 6 * swap 2 3 * swap 4 5, swap 0 1 * swap 2 6 * swap 6 3 * swap 4 5, swap 2 3 * swap 3 6]),
  (swap 1 3, [swap 0 4 * swap 4 6 * swap 1 3 * swap 2 5, swap 0 2 * swap 2 6 * swap 1 3 * swap 4 5, swap 4 5 * swap 5 6]),
  (swap 1 3 * swap 4 5, [swap 0 2 * swap 2 6 * swap 1 5 * swap 3 4, swap 2 6 * swap 4 5, swap 0 2 * swap 2 6]),
  (swap 0 1 * swap 2 3, [swap 0 1 * swap 2 3 * swap 4 6 * swap 6 5, swap 0 2 * swap 2 1 * swap 1 3 * swap 4 5, swap 0 1 * swap 4 5, swap 4 5 * swap 5 6]),
  (swap 0 1 * swap 2 3 * swap 4 5, [swap 0 3 * swap 3 1 * swap 1 2 * swap 4 5, swap 0 5 * swap 5 3 * swap 1 4 * swap 4 2]),
  (swap 0 2, [swap 0 2 * swap 1 6 * swap 6 4 * swap 3 5, swap 3 6 * swap 4 5, swap 4 5 * swap 5 6]),
  (swap 0 2 * swap 4 5, [swap 0 4 * swap 1 6 * swap 6 3 * swap 2 5, swap 0 2 * swap 3 6, swap 1 3 * swap 3 6]),
  (swap 0 2 * swap 1 3, [swap 0 3 * swap 1 2 * swap 4 6 * swap 6 5, swap 0 2 * swap 4 6, swap 4 5 * swap 5 6]),
  (swap 0 2 * swap 1 3 * swap 4 5, [swap 0 2 * swap 1 4 * swap 4 3 * swap 3 5, swap 0 4 * swap 4 1 * swap 2 5 * swap 5 3]),
  (swap 0 3 * swap 1 2, [swap 0 1 * swap 2 3 * swap 4 6 * swap 6 5, swap 0 2 * swap 2 3 * swap 3 1 * swap 5 6, swap 4 5 * swap 5 6]),
  (swap 0 3 * swap 1 2 * swap 4 5, [swap 0 4 * swap 4 3 * swap 3 5 * swap 1 2, swap 1 4 * swap 2 5])]

@[expose] def GC (t : S7) : List S7 :=
  ((GCtab.find? (fun p => decide (p.1 = t))).map Prod.snd).getD []

@[expose] def Good (a b : S7) : Bool :=
  ((GC a ++ GC b).any (fun g => decide (g.support.card = 3))) &&
    decide (reach (GC a ++ GC b) = Finset.univ)

theorem GC_ok : ∀ t ∈ T0list, t ^ 2 = 1 → t ≠ 1 → ∀ g ∈ GC t, sign g = 1 ∧ g * t = t * g := by
  have key : ∀ t ∈ T0list, t ^ 2 = 1 → t ≠ 1 →
      (GC t).all (fun g => decide (sign g = 1 ∧ g * t = t * g)) = true := by
    intro t ht
    rw [mem_T0list_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide +kernel
  intro t ht h2 h1 g hg
  have := List.all_eq_true.1 (key t ht h2 h1) g hg
  simpa using this

@[expose] def pairCond (a b : S7) : Bool :=
  decide (a ^ 2 = 1) && decide (b ^ 2 = 1) && decide (a ≠ 1) && decide (b ≠ 1) && decide (a ≠ b) &&
    decide (a * b = b * a) && !(decide (a ∈ V0list) && decide (b ∈ V0list))

theorem pair_good_bool :
    T0list.all (fun a => T0list.all (fun b => !pairCond a b || Good a b || Good a (a * b))) = true := by
  decide +kernel

theorem pair_good : ∀ a ∈ T0list, ∀ b ∈ T0list, a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
    a * b = b * a → ¬ (a ∈ V0list ∧ b ∈ V0list) → Good a b = true ∨ Good a (a * b) = true := by
  intro a ha b hb h2a h2b h1a h1b hab hcomm hV
  have h := List.all_eq_true.1 (List.all_eq_true.1 pair_good_bool a ha) b hb
  have hc : pairCond a b = true := by
    simp only [pairCond, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    refine ⟨⟨⟨⟨⟨⟨h2a, h2b⟩, h1a⟩, h1b⟩, hab⟩, hcomm⟩, ?_⟩
    by_contra hcon
    exact hV ⟨by_contra fun h => hcon (Or.inl h), by_contra fun h => hcon (Or.inr h)⟩
  rw [hc] at h
  simpa using h

end Table

end CFSG.GH74.GLS.IVK.Proofs2.A7Fin
