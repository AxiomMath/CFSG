module

public import CFSG.GH74.Generic.S45.LAltDefs

public section

namespace CFSG.GH74.Generic.BProg.B3.S45EvenN3Comb

open Equiv Equiv.Perm Subgroup CFSG.GH74.Generic.S45.LAlt
open scoped commutatorElement

variable {n : ℕ}

theorem swap_mul_swap_mem_alt {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  simp

theorem comm_swap_mul_swap {σ : Perm (Fin n)} {a b c d : Fin n} (ha : σ a = a) (hb : σ b = b)
    (hc : σ c = c) (hd : σ d = d) :
    (swap a b * swap c d) * σ = σ * (swap a b * swap c d) := by
  have h1 : swap a b * σ = σ * swap a b := by rw [mul_swap_eq_swap_mul σ a b, ha, hb]
  have h2 : swap c d * σ = σ * swap c d := by rw [mul_swap_eq_swap_mul σ c d, hc, hd]
  calc (swap a b * swap c d) * σ = swap a b * (swap c d * σ) := mul_assoc _ _ _
    _ = swap a b * (σ * swap c d) := by rw [h2]
    _ = (swap a b * σ) * swap c d := (mul_assoc _ _ _).symm
    _ = (σ * swap a b) * swap c d := by rw [h1]
    _ = σ * (swap a b * swap c d) := mul_assoc _ _ _

theorem conj_swap_mul_swap (σ : Perm (Fin n)) (a b c d : Fin n) :
    σ * (swap a b * swap c d) * σ⁻¹ = swap (σ a) (σ b) * swap (σ c) (σ d) := by
  rw [show σ * (swap a b * swap c d) * σ⁻¹ = (σ * swap a b * σ⁻¹) * (σ * swap c d * σ⁻¹) by group,
    ← swap_apply_apply, ← swap_apply_apply]

theorem comm_of_conj {σ g : Perm (Fin n)} (h : σ * g * σ⁻¹ = g) : g * σ = σ * g := by
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem comm_three_cycles {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ⁅swap a b * swap b c, swap a b * swap b d⁆ = swap a b * swap c d := by
  ext p
  simp only [commutatorElement_def, Perm.mul_apply, swap_inv, mul_inv_rev, swap_apply_def]
  grind

theorem comm_delta {α : Type*} [DecidableEq α] {x x' y y' z z' : α} (h1 : x ≠ x') (h2 : x ≠ y) (h3 : x ≠ y') (h4 : x ≠ z)
    (h5 : x ≠ z') (h6 : x' ≠ y) (h7 : x' ≠ y') (h8 : x' ≠ z) (h9 : x' ≠ z') (h10 : y ≠ y')
    (h11 : y ≠ z) (h12 : y ≠ z') (h13 : y' ≠ z) (h14 : y' ≠ z') (h15 : z ≠ z') :
    ⁅(swap x y * swap y z) * (swap x' y' * swap y' z'), swap x x' * swap y y'⁆ =
      swap x x' * swap z z' := by
  ext p
  simp only [commutatorElement_def, Perm.mul_apply, swap_inv, mul_inv_rev, swap_apply_def]
  grind

theorem commute_swap_swap {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Commute (swap a b) (swap c d) :=
  (Equiv.Perm.disjoint_swap_swap (by simp [hab, hac, had, hbc, hbd, hcd])).commute

theorem dblTransp_mul_self {g : Perm (Fin n)} (h : IsDblTransp g) : g * g = 1 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := h
  have hc := commute_swap_swap hab hac had hbc hbd hcd
  have h2 : (swap a b * swap c d) ^ 2 = 1 := by
    rw [hc.mul_pow, pow_two, pow_two, swap_mul_self, swap_mul_self, mul_one]
  rwa [pow_two] at h2

theorem comm_three_cycles_disjoint {x x' y y' z z' : Fin n} (h1 : x ≠ x') (h2 : x ≠ y) (h3 : x ≠ y')
    (h5 : x ≠ z') (h6 : x' ≠ y) (h7 : x' ≠ y') (h8 : x' ≠ z) (h10 : y ≠ y') (h11 : y ≠ z)
    (h12 : y ≠ z') (h13 : y' ≠ z) (h14 : y' ≠ z') (h15 : z ≠ z') :
    (swap x y * swap y z) * (swap x' y' * swap y' z') =
      (swap x' y' * swap y' z') * (swap x y * swap y z) :=
  (Commute.mul_left
    ((commute_swap_swap h2 h1 h3 h6.symm h10 h7).mul_right
      (commute_swap_swap h2 h3 h5 h10 h12 h14))
    ((commute_swap_swap h11 h6.symm h10 h8.symm h13.symm h7).mul_right
      (commute_swap_swap h11 h10 h12 h13.symm h15 h14))).eq

theorem klein_of_four_fixed {σ : Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (ha : σ a = a) (hb : σ b = b)
    (hc : σ c = c) (hd : σ d = d) :
    ∃ u v : Perm (Fin n), u ∈ ⁅centAlt σ, centAlt σ⁆ ∧ v ∈ ⁅centAlt σ, centAlt σ⁆ ∧
      u * v = v * u ∧ IsDblTransp u ∧ IsDblTransp v ∧ IsDblTransp (u * v) := by
  have hmem : ∀ {p q r : Fin n}, p ≠ q → q ≠ r → σ p = p → σ q = q → σ r = r →
      swap p q * swap q r ∈ centAlt σ := fun hpq hqr hp hq hr =>
    mem_centAlt.2 ⟨swap_mul_swap_mem_alt hpq hqr, comm_swap_mul_swap hp hq hq hr⟩
  have hbd' : b ≠ c := hbc
  refine ⟨swap a b * swap c d, swap a c * swap b d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← comm_three_cycles hab hac had hbc hbd hcd]
    exact Subgroup.commutator_mem_commutator (hmem hab hbc ha hb hc) (hmem hab hbd ha hb hd)
  · rw [← comm_three_cycles hac hab had hbc.symm hcd hbd]
    exact Subgroup.commutator_mem_commutator (hmem hac hbc.symm ha hc hb) (hmem hac hcd ha hc hd)
  · ext p
    simp only [Perm.mul_apply, swap_apply_def]
    grind
  · exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  · exact ⟨a, c, b, d, hac, hab, had, hbc.symm, hcd, hbd, rfl⟩
  · refine ⟨a, d, b, c, had, hab, hac, hbd.symm, hcd.symm, hbc, ?_⟩
    ext p
    simp only [Perm.mul_apply, swap_apply_def]
    grind

theorem swap_pairs_mem_centAlt {σ : Perm (Fin n)} {p p' q q' : Fin n} (hpp : p ≠ p') (hqq : q ≠ q')
    (hp : σ p = p') (hp' : σ p' = p) (hq : σ q = q') (hq' : σ q' = q) :
    swap p p' * swap q q' ∈ centAlt σ := by
  refine mem_centAlt.2 ⟨swap_mul_swap_mem_alt hpp hqq, comm_of_conj ?_⟩
  rw [conj_swap_mul_swap, hp, hp', hq, hq', swap_comm p' p, swap_comm q' q]

theorem delta_mem_centAlt {σ : Perm (Fin n)} {p p' q q' r r' : Fin n} (hpp' : p ≠ p') (hpq : p ≠ q)
    (hpq' : p ≠ q') (hpr' : p ≠ r') (hp'q : p' ≠ q) (hp'q' : p' ≠ q') (hp'r : p' ≠ r)
    (hqq' : q ≠ q') (hqr : q ≠ r) (hqr' : q ≠ r') (hq'r : q' ≠ r)
    (hq'r' : q' ≠ r') (hrr' : r ≠ r') (hp : σ p = p') (hp' : σ p' = p) (hq : σ q = q')
    (hq' : σ q' = q) (hr : σ r = r') (hr' : σ r' = r) :
    (swap p q * swap q r) * (swap p' q' * swap q' r') ∈ centAlt σ := by
  refine mem_centAlt.2 ⟨mul_mem (swap_mul_swap_mem_alt hpq hqr)
    (swap_mul_swap_mem_alt hp'q' hq'r'), comm_of_conj ?_⟩
  rw [show σ * ((swap p q * swap q r) * (swap p' q' * swap q' r')) * σ⁻¹ =
      (σ * (swap p q * swap q r) * σ⁻¹) * (σ * (swap p' q' * swap q' r') * σ⁻¹) by group,
    conj_swap_mul_swap, conj_swap_mul_swap, hp, hp', hq, hq', hr, hr']
  exact (comm_three_cycles_disjoint hpp' hpq hpq' hpr' hp'q hp'q' hp'r hqq' hqr hqr' hq'r hq'r'
    hrr').symm

theorem klein_of_three_pairs {σ : Perm (Fin n)} {x x' y y' z z' : Fin n} (h1 : x ≠ x') (h2 : x ≠ y)
    (h3 : x ≠ y') (h4 : x ≠ z) (h5 : x ≠ z') (h6 : x' ≠ y) (h7 : x' ≠ y') (h8 : x' ≠ z)
    (h9 : x' ≠ z') (h10 : y ≠ y') (h11 : y ≠ z) (h12 : y ≠ z') (h13 : y' ≠ z) (h14 : y' ≠ z')
    (h15 : z ≠ z') (hx : σ x = x') (hx' : σ x' = x) (hy : σ y = y') (hy' : σ y' = y)
    (hz : σ z = z') (hz' : σ z' = z) :
    ∃ u v : Perm (Fin n), u ∈ ⁅centAlt σ, centAlt σ⁆ ∧ v ∈ ⁅centAlt σ, centAlt σ⁆ ∧
      u * v = v * u ∧ IsDblTransp u ∧ IsDblTransp v ∧ IsDblTransp (u * v) := by
  have hu : ⁅(swap x z * swap z y) * (swap x' z' * swap z' y'), swap x x' * swap z z'⁆ =
      swap x x' * swap y y' := by
    refine comm_delta ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      first | assumption | exact Ne.symm ‹_›
  have hv : ⁅(swap x y * swap y z) * (swap x' y' * swap y' z'), swap x x' * swap y y'⁆ =
      swap x x' * swap z z' := comm_delta h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  refine ⟨swap x x' * swap y y', swap x x' * swap z z', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hu]
    refine Subgroup.commutator_mem_commutator (delta_mem_centAlt ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ hx hx' hz hz' hy hy') (swap_pairs_mem_centAlt h1 h15 hx hx' hz hz') <;>
      first | assumption | exact Ne.symm ‹_›
  · rw [← hv]
    refine Subgroup.commutator_mem_commutator (delta_mem_centAlt h1 h2 h3 h5 h6 h7 h8 h10 h11 h12
      h13 h14 h15 hx hx' hy hy' hz hz') (swap_pairs_mem_centAlt h1 h10 hx hx' hy hy')
  · ext p
    simp only [Perm.mul_apply, swap_apply_def]
    grind
  · exact ⟨x, x', y, y', h1, h2, h3, h6, h7, h10, rfl⟩
  · exact ⟨x, x', z, z', h1, h4, h5, h8, h9, h15, rfl⟩
  · refine ⟨y, y', z, z', h10, h11, h12, h13, h14, h15, ?_⟩
    ext p
    simp only [Perm.mul_apply, swap_apply_def]
    grind

theorem exists_klein_commutators {σ : Perm (Fin n)} (hσ : σ * σ = 1) (hn : 8 ≤ n) :
    ∃ u v : Perm (Fin n), u ∈ ⁅centAlt σ, centAlt σ⁆ ∧ v ∈ ⁅centAlt σ, centAlt σ⁆ ∧
      u * v = v * u ∧ IsDblTransp u ∧ IsDblTransp v ∧ IsDblTransp (u * v) := by
  classical
  have hσσ : ∀ p, σ (σ p) = p := sigma_sq_apply hσ
  set F : Finset (Fin n) := Finset.univ.filter (fun p => σ p = p) with hF
  set S : Finset (Fin n) := Finset.univ.filter (fun p => ¬ σ p = p) with hS
  have hcard : F.card + S.card = n := by
    rw [hF, hS, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  by_cases h4 : 4 ≤ F.card
  · obtain ⟨a, haF, -⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := (∅ : Finset (Fin n)))
      (t := F) (by simp only [Finset.card_empty]; omega)
    obtain ⟨b, hbF, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a}) (t := F)
      (by have := Finset.card_singleton a; omega)
    obtain ⟨c, hcF, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, b}) (t := F)
      (by have := Finset.card_le_two (a := a) (b := b); omega)
    obtain ⟨d, hdF, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, b, c}) (t := F)
      (by have := Finset.card_le_three (a := a) (b := b) (c := c); omega)
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at haF hbF hcF hdF
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hb hc hd
    exact klein_of_four_fixed (fun h => hb h.symm) (fun h => hc.1 h.symm) (fun h => hd.1 h.symm)
      (fun h => hc.2 h.symm) (fun h => hd.2.1 h.symm) (fun h => hd.2.2 h.symm) haF hbF hcF hdF
  · have h5 : 5 ≤ S.card := by omega
    obtain ⟨i, hiS, -⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := (∅ : Finset (Fin n)))
      (t := S) (by simp only [Finset.card_empty]; omega)
    obtain ⟨j, hjS, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {i, σ i}) (t := S)
      (by have := Finset.card_le_two (a := i) (b := σ i); omega)
    obtain ⟨k, hkS, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {i, σ i, j, σ j}) (t := S)
      (by have := Finset.card_le_four (a := i) (b := σ i) (c := j) (d := σ j); omega)
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hiS hjS hkS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj hk
    have e1 := hσσ i
    have e2 := hσσ j
    have e3 := hσσ k
    refine klein_of_three_pairs (σ := σ) (x := i) (x' := σ i) (y := j) (y' := σ j) (z := k)
      (z' := σ k) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl e1 rfl e2 rfl e3 <;> grind

end CFSG.GH74.Generic.BProg.B3.S45EvenN3Comb
