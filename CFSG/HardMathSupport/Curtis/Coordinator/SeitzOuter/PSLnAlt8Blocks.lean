module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open Equiv Equiv.Perm

@[expose] def cyc3 (a b c : Fin 8) : Perm (Fin 8) := swap a b * swap b c

@[expose] def alt8Init : List (Fin 8 × Fin 8 × Fin 8) := [
  (0, 1, 2),
  (0, 1, 6),
  (0, 1, 7),
  (0, 2, 1),
  (0, 2, 6),
  (0, 2, 7),
  (0, 6, 1),
  (0, 6, 2),
  (0, 6, 7),
  (0, 7, 1),
  (0, 7, 2),
  (0, 7, 6),
  (1, 2, 6),
  (1, 2, 7),
  (1, 6, 2),
  (1, 6, 7),
  (1, 7, 2),
  (1, 7, 6),
  (2, 6, 7),
  (2, 7, 6),
  (3, 4, 5),
  (3, 4, 6),
  (3, 4, 7),
  (3, 5, 4),
  (3, 5, 6),
  (3, 5, 7),
  (3, 6, 4),
  (3, 6, 5),
  (3, 6, 7),
  (3, 7, 4),
  (3, 7, 5),
  (3, 7, 6),
  (4, 5, 6),
  (4, 5, 7),
  (4, 6, 5),
  (4, 6, 7),
  (4, 7, 5),
  (4, 7, 6),
  (5, 6, 7),
  (5, 7, 6)
]

@[expose] def alt8Steps : List ((Fin 8 × Fin 8 × Fin 8) × (Fin 8 × Fin 8 × Fin 8) × (Fin 8 × Fin 8 × Fin 8)) := [
  ((0, 3, 4), (0, 1, 6), (3, 4, 6)),
  ((0, 3, 5), (0, 1, 6), (3, 5, 6)),
  ((0, 4, 3), (0, 1, 6), (3, 6, 4)),
  ((0, 5, 3), (0, 1, 6), (3, 6, 5)),
  ((0, 7, 3), (0, 1, 6), (3, 6, 7)),
  ((0, 3, 7), (0, 1, 6), (3, 7, 6)),
  ((0, 4, 5), (0, 1, 6), (4, 5, 6)),
  ((0, 5, 4), (0, 1, 6), (4, 6, 5)),
  ((0, 7, 4), (0, 1, 6), (4, 6, 7)),
  ((0, 4, 7), (0, 1, 6), (4, 7, 6)),
  ((0, 7, 5), (0, 1, 6), (5, 6, 7)),
  ((0, 5, 7), (0, 1, 6), (5, 7, 6)),
  ((0, 3, 6), (0, 1, 7), (3, 6, 7)),
  ((0, 6, 3), (0, 1, 7), (3, 7, 6)),
  ((0, 4, 6), (0, 1, 7), (4, 6, 7)),
  ((0, 6, 4), (0, 1, 7), (4, 7, 6)),
  ((0, 5, 6), (0, 1, 7), (5, 6, 7)),
  ((0, 6, 5), (0, 1, 7), (5, 7, 6)),
  ((1, 3, 4), (0, 1, 7), (0, 3, 4)),
  ((1, 3, 5), (0, 1, 7), (0, 3, 5)),
  ((1, 4, 3), (0, 1, 7), (0, 4, 3)),
  ((1, 5, 3), (0, 1, 7), (0, 5, 3)),
  ((0, 3, 1), (0, 1, 7), (0, 7, 3)),
  ((0, 1, 3), (0, 1, 7), (0, 3, 7)),
  ((1, 4, 5), (0, 1, 7), (0, 4, 5)),
  ((1, 5, 4), (0, 1, 7), (0, 5, 4)),
  ((0, 4, 1), (0, 1, 7), (0, 7, 4)),
  ((0, 1, 4), (0, 1, 7), (0, 4, 7)),
  ((0, 5, 1), (0, 1, 7), (0, 7, 5)),
  ((0, 1, 5), (0, 1, 7), (0, 5, 7)),
  ((2, 3, 4), (0, 2, 1), (0, 3, 4)),
  ((2, 3, 5), (0, 2, 1), (0, 3, 5)),
  ((2, 4, 3), (0, 2, 1), (0, 4, 3)),
  ((2, 5, 3), (0, 2, 1), (0, 5, 3)),
  ((2, 7, 3), (0, 2, 1), (0, 7, 3)),
  ((2, 3, 7), (0, 2, 1), (0, 3, 7)),
  ((2, 4, 5), (0, 2, 1), (0, 4, 5)),
  ((2, 5, 4), (0, 2, 1), (0, 5, 4)),
  ((2, 7, 4), (0, 2, 1), (0, 7, 4)),
  ((2, 4, 7), (0, 2, 1), (0, 4, 7)),
  ((2, 7, 5), (0, 2, 1), (0, 7, 5)),
  ((2, 5, 7), (0, 2, 1), (0, 5, 7)),
  ((2, 3, 6), (0, 2, 1), (0, 3, 6)),
  ((2, 6, 3), (0, 2, 1), (0, 6, 3)),
  ((2, 4, 6), (0, 2, 1), (0, 4, 6)),
  ((2, 6, 4), (0, 2, 1), (0, 6, 4)),
  ((2, 5, 6), (0, 2, 1), (0, 5, 6)),
  ((2, 6, 5), (0, 2, 1), (0, 6, 5)),
  ((0, 2, 3), (0, 2, 1), (0, 3, 1)),
  ((0, 3, 2), (0, 2, 1), (0, 1, 3)),
  ((0, 2, 4), (0, 2, 1), (0, 4, 1)),
  ((0, 4, 2), (0, 2, 1), (0, 1, 4)),
  ((0, 2, 5), (0, 2, 1), (0, 5, 1)),
  ((0, 5, 2), (0, 2, 1), (0, 1, 5)),
  ((1, 2, 3), (0, 2, 6), (0, 3, 1)),
  ((1, 3, 2), (0, 2, 6), (0, 1, 3)),
  ((1, 2, 4), (0, 2, 6), (0, 4, 1)),
  ((1, 4, 2), (0, 2, 6), (0, 1, 4)),
  ((1, 2, 5), (0, 2, 6), (0, 5, 1)),
  ((1, 5, 2), (0, 2, 6), (0, 1, 5)),
  ((1, 7, 3), (0, 2, 7), (1, 2, 3)),
  ((1, 3, 7), (0, 2, 7), (1, 3, 2)),
  ((1, 7, 4), (0, 2, 7), (1, 2, 4)),
  ((1, 4, 7), (0, 2, 7), (1, 4, 2)),
  ((1, 7, 5), (0, 2, 7), (1, 2, 5)),
  ((1, 5, 7), (0, 2, 7), (1, 5, 2)),
  ((1, 6, 3), (0, 6, 1), (0, 3, 6)),
  ((1, 3, 6), (0, 6, 1), (0, 6, 3)),
  ((1, 6, 4), (0, 6, 1), (0, 4, 6)),
  ((1, 4, 6), (0, 6, 1), (0, 6, 4)),
  ((1, 6, 5), (0, 6, 1), (0, 5, 6)),
  ((1, 5, 6), (0, 6, 1), (0, 6, 5))
]

@[expose] def cycT (t : Fin 8 × Fin 8 × Fin 8) : Perm (Fin 8) := cyc3 t.1 t.2.1 t.2.2

@[expose] def altValid : List (Fin 8 × Fin 8 × Fin 8) →
    List ((Fin 8 × Fin 8 × Fin 8) × (Fin 8 × Fin 8 × Fin 8) × (Fin 8 × Fin 8 × Fin 8)) → Bool
  | _, [] => true
  | known, (c, g, x) :: rest =>
      decide (g ∈ known) && decide (x ∈ known) && decide (cycT c = cycT g * cycT x * (cycT g)⁻¹) &&
        altValid (c :: known) rest

theorem altValid_all : altValid alt8Init alt8Steps = true := by decide +kernel

theorem alt8_distinct : ∀ t ∈ alt8Init ++ alt8Steps.map (·.1), t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 := by
  decide +kernel

theorem alt8_cover : ∀ a b c : Fin 8, [a, b, c].Nodup →
    ∃ t ∈ alt8Init ++ alt8Steps.map (·.1), cyc3 a b c = cycT t := by decide +kernel

theorem chain_mem (H : Subgroup (Perm (Fin 8))) :
    ∀ (steps : List ((Fin 8 × Fin 8 × Fin 8) × (Fin 8 × Fin 8 × Fin 8) × (Fin 8 × Fin 8 × Fin 8)))
      (known : List (Fin 8 × Fin 8 × Fin 8)), (∀ t ∈ known, cycT t ∈ H) → altValid known steps = true →
        ∀ t ∈ known ++ steps.map (·.1), cycT t ∈ H := by
  intro steps
  induction steps with
  | nil => intro known hk _ t ht; simpa using hk t (by simpa using ht)
  | cons s rest ih =>
    obtain ⟨c, g, x⟩ := s
    intro known hk hv
    simp only [altValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨hg, hx⟩, hc⟩, hrest⟩ := hv
    have hcH : cycT c ∈ H := by
      rw [hc]
      exact H.mul_mem (H.mul_mem (hk g hg) (hk x hx)) (H.inv_mem (hk g hg))
    have := ih (c :: known) (by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hcH
      · exact hk t ht) hrest
    intro t ht
    have h2 := this t (by
      simp only [List.mem_append, List.mem_cons, List.map_cons] at ht ⊢
      tauto)
    exact h2

theorem isThreeCycle_mem_of_blocks (H : Subgroup (Perm (Fin 8)))
    (hinit : ∀ t ∈ alt8Init, cycT t ∈ H) {g : Perm (Fin 8)} (hg : g.IsThreeCycle) : g ∈ H := by
  have hall := chain_mem H alt8Steps alt8Init hinit altValid_all
  obtain ⟨a, ha⟩ : g.support.Nonempty := by
    rw [← Finset.card_pos, hg.card_support]; norm_num
  have hgeq : g = swap a (g a) * swap (g a) (g (g a)) :=
    (hg.eq_swap_mul_swap_iff_mem_support).mpr ha
  have hnd : [a, g a, g (g a)].Nodup := (hg.nodup_iff_mem_support).mpr ha
  obtain ⟨t, ht, hteq⟩ := alt8_cover a (g a) (g (g a)) hnd
  have hmem : cyc3 a (g a) (g (g a)) ∈ H := by
    rw [hteq]
    exact hall t ht
  rw [hgeq]
  exact hmem

theorem alt8_le_of_blocks (H : Subgroup (Perm (Fin 8))) (hinit : ∀ t ∈ alt8Init, cycT t ∈ H) :
    alternatingGroup (Fin 8) ≤ H := by
  rw [← closure_three_cycles_eq_alternating, Subgroup.closure_le]
  exact fun g hg => isThreeCycle_mem_of_blocks H hinit hg

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
