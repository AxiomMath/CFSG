module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.GF2Type.Smith1979W3.CaseD

open Equiv Equiv.Perm Finset

theorem support_swap_mul_swap_of_nodup {α : Type*} [DecidableEq α] [Fintype α] {a b c d : α}
    (h : [a, b, c, d].Nodup) : (swap a b * swap c d).support = {a, b, c, d} := by
  have hab : a ≠ b := by rintro rfl; simp at h
  have hcd : c ≠ d := by rintro rfl; simp at h
  rw [(disjoint_swap_swap h).support_mul, support_swap hab, support_swap hcd]
  ext x
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

theorem support_std : (swap (0 : Fin 8) 1 * swap 2 3).support = {0, 1, 2, 3} :=
  support_swap_mul_swap_of_nodup (by decide)

@[expose] def IsDT (t : Perm (Fin 8)) : Prop :=
  ∃ a b c d : Fin 8, [a, b, c, d].Nodup ∧ t = swap a b * swap c d

theorem IsDT.conj {t : Perm (Fin 8)} (h : IsDT t) (g : Perm (Fin 8)) : IsDT (g * t * g⁻¹) := by
  obtain ⟨a, b, c, d, hnd, rfl⟩ := h
  refine ⟨g a, g b, g c, g d, ?_, ?_⟩
  · simpa using hnd.map g.injective
  · rw [swap_apply_apply g a b, swap_apply_apply g c d]
    group

theorem IsDT.card_support {t : Perm (Fin 8)} (h : IsDT t) : t.support.card = 4 := by
  obtain ⟨a, b, c, d, hnd, rfl⟩ := h
  have hc := cycleType_swap_mul_swap_of_nodup hnd
  have hsum := sum_cycleType (swap a b * swap c d)
  rw [hc] at hsum
  simpa using hsum.symm

theorem IsDT.ne_one {t : Perm (Fin 8)} (h : IsDT t) : t ≠ 1 := by
  intro h1
  have := h.card_support
  rw [h1, support_one] at this
  simp at this

theorem IsDT.exists_conj_std {t : Perm (Fin 8)} (h : IsDT t) :
    ∃ g : Perm (Fin 8), t = g * (swap 0 1 * swap 2 3) * g⁻¹ := by
  obtain ⟨a, b, c, d, hnd, rfl⟩ := h
  have hstd : (swap (0 : Fin 8) 1 * swap 2 3).cycleType = {2, 2} :=
    cycleType_swap_mul_swap_of_nodup (by decide : ([0, 1, 2, 3] : List (Fin 8)).Nodup)
  have ht : (swap a b * swap c d).cycleType = {2, 2} := cycleType_swap_mul_swap_of_nodup hnd
  have hconj : IsConj (swap 0 1 * swap 2 3) (swap a b * swap c d) :=
    isConj_iff_cycleType_eq.2 (by rw [hstd, ht])
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  exact ⟨g, hg.symm⟩

private abbrev tableOneHyp (a b c d : Fin 8) : Prop :=
  [a, b, c, d].Nodup ∧ (({0, 1, 2, 3} : Finset (Fin 8)) ∩ {a, b, c, d}).card = 1

private def tableOneCheck : Bool :=
  (List.finRange 8).all fun a =>
    (List.finRange 8).all fun b =>
      (List.finRange 8).all fun c =>
        (List.finRange 8).all fun d =>
          !(decide (tableOneHyp a b c d)) ||
            decide ((((swap (0 : Fin 8) 1 * swap 2 3) * (swap a b * swap c d)) ^ 2).support.card =
              3)

private theorem tableOneCheck_eq : tableOneCheck = true := by
  decide +kernel

theorem table_one_std : ∀ a b c d : Fin 8, [a, b, c, d].Nodup →
    (({0, 1, 2, 3} : Finset (Fin 8)) ∩ {a, b, c, d}).card = 1 →
    (((swap (0 : Fin 8) 1 * swap 2 3) * (swap a b * swap c d)) ^ 2).support.card = 3 := by
  intro a b c d hnd hcard
  have h := tableOneCheck_eq
  simp only [tableOneCheck, List.all_eq_true] at h
  have h1 := h a (List.mem_finRange a) b (List.mem_finRange b) c (List.mem_finRange c)
    d (List.mem_finRange d)
  rw [decide_eq_true (show tableOneHyp a b c d from ⟨hnd, hcard⟩),
    Bool.not_true, Bool.false_or] at h1
  exact of_decide_eq_true h1

private abbrev tableThreeHyp (a b c d : Fin 8) : Prop :=
  [a, b, c, d].Nodup ∧ (({0, 1, 2, 3} : Finset (Fin 8)) ∩ {a, b, c, d}).card = 3

private def tableThreeCheck : Bool :=
  (List.finRange 8).all fun a =>
    (List.finRange 8).all fun b =>
      (List.finRange 8).all fun c =>
        (List.finRange 8).all fun d =>
          !(decide (tableThreeHyp a b c d)) ||
            (decide (((swap (0 : Fin 8) 1 * swap 2 3) * (swap a b * swap c d)).support.card = 3) ||
             decide ((((swap (0 : Fin 8) 1 * swap 2 3) * (swap a b * swap c d)) ^ 5 = 1) ∧
               ((swap (0 : Fin 8) 1 * swap 2 3) * (swap a b * swap c d)).support.card = 5))

private theorem tableThreeCheck_eq : tableThreeCheck = true := by
  decide +kernel

theorem table_three_std : ∀ a b c d : Fin 8, [a, b, c, d].Nodup →
    (({0, 1, 2, 3} : Finset (Fin 8)) ∩ {a, b, c, d}).card = 3 →
    ((swap (0 : Fin 8) 1 * swap 2 3) * (swap a b * swap c d)).support.card = 3 ∨
    ((((swap (0 : Fin 8) 1 * swap 2 3) * (swap a b * swap c d)) ^ 5 = 1) ∧
      ((swap (0 : Fin 8) 1 * swap 2 3) * (swap a b * swap c d)).support.card = 5) := by
  intro a b c d hnd hcard
  have h := tableThreeCheck_eq
  simp only [tableThreeCheck, List.all_eq_true] at h
  have h1 := h a (List.mem_finRange a) b (List.mem_finRange b) c (List.mem_finRange c)
    d (List.mem_finRange d)
  rw [decide_eq_true (show tableThreeHyp a b c d from ⟨hnd, hcard⟩),
    Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  rcases h1 with h3 | h5
  · exact Or.inl (of_decide_eq_true h3)
  · exact Or.inr (of_decide_eq_true h5)

theorem table_one {t t' : Perm (Fin 8)} (ht : IsDT t) (ht' : IsDT t')
    (h : (t.support ∩ t'.support).card = 1) : ((t * t') ^ 2).IsThreeCycle := by
  obtain ⟨g, hg⟩ := ht.exists_conj_std
  have hu : IsDT (g⁻¹ * t' * g) := by
    have := ht'.conj g⁻¹
    simpa using this
  obtain ⟨a, b, c, d, hnd, hu_eq⟩ := hu
  have ht_supp : t.support = (({0, 1, 2, 3} : Finset (Fin 8))).map g.toEmbedding := by
    rw [hg, support_conj, support_std]
  have ht'_supp : t'.support = (({a, b, c, d} : Finset (Fin 8))).map g.toEmbedding := by
    have h1 : t' = g * (g⁻¹ * t' * g) * g⁻¹ := by group
    rw [h1, support_conj, hu_eq, support_swap_mul_swap_of_nodup hnd]
  have hmap : (({0, 1, 2, 3} : Finset (Fin 8)) ∩ ({a, b, c, d} : Finset (Fin 8))).map
      g.toEmbedding = t.support ∩ t'.support := by
    rw [Finset.map_inter, ← ht_supp, ← ht'_supp]
  have hinter : (({0, 1, 2, 3} : Finset (Fin 8)) ∩ ({a, b, c, d} : Finset (Fin 8))).card = 1 := by
    have := congrArg Finset.card hmap
    rw [Finset.card_map, h] at this
    exact this
  have h3 := card_support_eq_three_iff.1 (table_one_std a b c d hnd hinter)
  have ht'eq : t' = g * (swap a b * swap c d) * g⁻¹ := by
    rw [← hu_eq]; group
  have hpow : (t * t') ^ 2
      = g * ((swap 0 1 * swap 2 3) * (swap a b * swap c d)) ^ 2 * g⁻¹ := by
    rw [hg, ht'eq, conj_mul, conj_pow]
  change ((t * t') ^ 2).cycleType = {3}
  rw [hpow, cycleType_conj]
  exact h3.cycleType

theorem table_three {t t' : Perm (Fin 8)} (ht : IsDT t) (ht' : IsDT t')
    (h : (t.support ∩ t'.support).card = 3) :
    (t * t').IsThreeCycle ∨ ((t * t').IsCycle ∧ (t * t').support.card = 5) := by
  obtain ⟨g, hg⟩ := ht.exists_conj_std
  have hu : IsDT (g⁻¹ * t' * g) := by
    have := ht'.conj g⁻¹
    simpa using this
  obtain ⟨a, b, c, d, hnd, hu_eq⟩ := hu
  have ht_supp : t.support = (({0, 1, 2, 3} : Finset (Fin 8))).map g.toEmbedding := by
    rw [hg, support_conj, support_std]
  have ht'_supp : t'.support = (({a, b, c, d} : Finset (Fin 8))).map g.toEmbedding := by
    have h1 : t' = g * (g⁻¹ * t' * g) * g⁻¹ := by group
    rw [h1, support_conj, hu_eq, support_swap_mul_swap_of_nodup hnd]
  have hmap : (({0, 1, 2, 3} : Finset (Fin 8)) ∩ ({a, b, c, d} : Finset (Fin 8))).map
      g.toEmbedding = t.support ∩ t'.support := by
    rw [Finset.map_inter, ← ht_supp, ← ht'_supp]
  have hinter : (({0, 1, 2, 3} : Finset (Fin 8)) ∩ ({a, b, c, d} : Finset (Fin 8))).card = 3 := by
    have := congrArg Finset.card hmap
    rw [Finset.card_map, h] at this
    exact this
  have ht'eq : t' = g * (swap a b * swap c d) * g⁻¹ := by
    rw [← hu_eq]; group
  have ht_eq : t * t' = g * ((swap 0 1 * swap 2 3) * (swap a b * swap c d)) * g⁻¹ := by
    rw [hg, ht'eq]; group
  rcases table_three_std a b c d hnd hinter with h3 | ⟨h5, hcard5⟩
  · left
    change (t * t').cycleType = {3}
    rw [ht_eq, cycleType_conj]
    exact (card_support_eq_three_iff.1 h3).cycleType
  · right
    have hσ : (swap 0 1 * swap 2 3) * (swap a b * swap c d) ≠ 1 := by
      intro h1
      rw [h1, support_one] at hcard5
      simp at hcard5
    have hdvd : orderOf ((swap 0 1 * swap 2 3) * (swap a b * swap c d)) ∣ 5 :=
      orderOf_dvd_iff_pow_eq_one.2 h5
    have hone : orderOf ((swap 0 1 * swap 2 3) * (swap a b * swap c d)) ≠ 1 := by
      intro ho
      exact hσ (orderOf_eq_one_iff.1 ho)
    have ho_eq : orderOf ((swap 0 1 * swap 2 3) * (swap a b * swap c d)) = 5 := by
      rcases Nat.prime_five.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact absurd h1 hone
      · exact h1
    have hprime : Nat.Prime (orderOf ((swap 0 1 * swap 2 3) * (swap a b * swap c d))) := by
      rw [ho_eq]; exact Nat.prime_five
    have hcyc : ((swap 0 1 * swap 2 3) * (swap a b * swap c d)).IsCycle := by
      apply isCycle_of_prime_order hprime
      rw [hcard5, ho_eq]
      norm_num
    constructor
    · change (t * t').IsCycle
      rw [ht_eq]
      exact hcyc.conj
    · rw [ht_eq, support_conj, Finset.card_map]
      exact hcard5

theorem IsDT.card_inter_le {t t' : Perm (Fin 8)} (ht : IsDT t) :
    (t.support ∩ t'.support).card ≤ 4 := by
  calc (t.support ∩ t'.support).card ≤ t.support.card :=
        Finset.card_le_card Finset.inter_subset_left
    _ = 4 := ht.card_support

end CFSG.GF2Type.Smith1979W3.CaseD
