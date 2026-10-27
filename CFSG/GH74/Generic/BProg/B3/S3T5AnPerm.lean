module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Zify

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5An

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem apply_eq_of_sq_apply_eq {x : Perm α} (hx : Odd (orderOf x)) {a : α}
    (h : (x * x) a = a) : x a = a := by
  obtain ⟨k, hk⟩ := hx
  have h1 : (x * x) ^ (k + 1) = x := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [← h1]
  exact pow_apply_eq_self_of_apply_eq_self h _

section OddNormal

variable {N : Subgroup (Perm α)} {f : Perm α}

omit [DecidableEq α] in
theorem odd_orderOf_of_mem (hN : Odd (Nat.card N)) {y : Perm α} (hy : y ∈ N) :
    Odd (orderOf y) := by
  have h := orderOf_dvd_natCard (⟨y, hy⟩ : N)
  rw [Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat hN h

omit [DecidableEq α] in
theorem eq_one_of_mul_self (hN : Odd (Nat.card N)) {y : Perm α} (hy : y ∈ N)
    (hyy : y * y = 1) : y = 1 := by
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hyy)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · have h3 := odd_orderOf_of_mem hN hy
    rw [h] at h3
    exact absurd h3 (by decide)

theorem swap_mul_comm {p q : α} (h : f * swap p q * f⁻¹ = swap p q) :
    swap p q * f = f * swap p q := by
  calc swap p q * f = f * swap p q * f⁻¹ * f := by rw [h]
    _ = f * swap p q := by group

theorem apply_eq_of_moved (hN : Odd (Nat.card N)) (hf : f * f = 1)
    (hNC : ∀ y ∈ N, y * f = f * y)
    (hnorm : ∀ g : Perm α, g * f = f * g → ∀ y ∈ N, g * y * g⁻¹ ∈ N) {x : Perm α} (hx : x ∈ N)
    {a : α} (ha : f a ≠ a) : x a = a := by
  have hff : ∀ p, f (f p) = p := fun p => by rw [← Perm.mul_apply, hf, Perm.one_apply]
  have hxf : ∀ p, x (f p) = f (x p) := fun p => by
    rw [← Perm.mul_apply, ← Perm.mul_apply, hNC x hx]
  have hτ : swap a (f a) * f = f * swap a (f a) :=
    swap_mul_comm (by rw [← swap_apply_apply, hff, swap_comm])
  by_contra hxa
  by_cases hxab : x a = f a
  · have hxb : x (f a) = a := by rw [hxf, hxab, hff]
    exact hxa (apply_eq_of_sq_apply_eq (odd_orderOf_of_mem hN hx)
      (by rw [Perm.mul_apply, hxab, hxb]))
  have hda : x (f a) ≠ a := fun h => by
    rw [hxf] at h
    have h' := congrArg f h
    rw [hff] at h'
    exact hxab h'
  have hdb : x (f a) ≠ f a := fun h => by
    rw [hxf] at h
    exact hxa (f.injective h)
  have hab : a ≠ f a := fun h => ha h.symm
  have hcd : x a ≠ x (f a) := fun h => hab (x.injective h)
  have hw : swap (x a) (x (f a)) * swap a (f a) ∈ N := by
    have h2 := mul_mem hx (hnorm (swap a (f a)) hτ x⁻¹ (inv_mem hx))
    rwa [swap_inv, ← mul_assoc, ← mul_assoc, ← swap_apply_apply] at h2
  have hcomm : Commute (swap (x a) (x (f a))) (swap a (f a)) :=
    (disjoint_swap_swap (by simp [hcd, hxa, hxab, hda, hdb, hab])).commute
  have hww : swap (x a) (x (f a)) * swap a (f a) * (swap (x a) (x (f a)) * swap a (f a)) = 1 := by
    calc swap (x a) (x (f a)) * swap a (f a) * (swap (x a) (x (f a)) * swap a (f a))
        = swap (x a) (x (f a)) * (swap a (f a) * swap (x a) (x (f a))) * swap a (f a) := by
          group
      _ = swap (x a) (x (f a)) * (swap (x a) (x (f a)) * swap a (f a)) * swap a (f a) := by
          rw [hcomm.eq]
      _ = 1 := by rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]
  have h2 : (swap (x a) (x (f a)) * swap a (f a)) a = f a := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hxab) (Ne.symm hdb)]
  rw [eq_one_of_mul_self hN hw hww, Perm.one_apply] at h2
  exact hab h2

theorem swap_conj_prod {a c e d : α} (hac : a ≠ c) (hae : a ≠ e) (had : a ≠ d) (hce : c ≠ e)
    (hcd : c ≠ d) (hed : e ≠ d) :
    swap c e * swap a c * (swap c d * (swap c e * swap a c) * (swap c d)⁻¹) =
      swap a c * swap e d := by
  have hca := hac.symm
  have hea := hae.symm
  have hda := had.symm
  have hec := hce.symm
  have hdc := hcd.symm
  have hde := hed.symm
  rw [swap_inv]
  ext p
  simp only [Perm.mul_apply]
  rcases eq_or_ne p a with rfl | hpa
  · simp [swap_apply_def, *]
  rcases eq_or_ne p c with rfl | hpc
  · simp [swap_apply_def, *]
  rcases eq_or_ne p e with rfl | hpe
  · simp [swap_apply_def, *]
  rcases eq_or_ne p d with rfl | hpd
  · simp [swap_apply_def, *]
  simp [swap_apply_of_ne_of_ne, *]

theorem card_fix_eq_three [Fintype α] (hN : Odd (Nat.card N)) (hf : f * f = 1)
    (hNC : ∀ y ∈ N, y * f = f * y)
    (hnorm : ∀ g : Perm α, g * f = f * g → ∀ y ∈ N, g * y * g⁻¹ ∈ N) {x : Perm α} (hx : x ∈ N)
    (hx1 : x ≠ 1) : (Finset.univ.filter fun p => f p = p).card = 3 := by
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ a := by
    by_contra h
    push Not at h
    exact hx1 (Equiv.ext h)
  have hfa : f a = a := by
    by_contra h
    exact ha (apply_eq_of_moved hN hf hNC hnorm hx h)
  have hxf : ∀ p, x (f p) = f (x p) := fun p => by
    rw [← Perm.mul_apply, ← Perm.mul_apply, hNC x hx]
  have hfc : f (x a) = x a := by rw [← hxf, hfa]
  have hfe : f (x (x a)) = x (x a) := by rw [← hxf, hfc]
  have hec : x (x a) ≠ x a := fun h => ha (x.injective h)
  have hea : x (x a) ≠ a := fun h =>
    ha (apply_eq_of_sq_apply_eq (odd_orderOf_of_mem hN hx) (by rw [Perm.mul_apply, h]))
  have hcf : ∀ p q, f p = p → f q = q → swap p q * f = f * swap p q := fun p q hp hq =>
    swap_mul_comm (by rw [← swap_apply_apply, hp, hq])
  have hsub : ({a, x a, x (x a)} : Finset α) ⊆ Finset.univ.filter fun p => f p = p := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> simp [hfa, hfc, hfe]
  have hcard3 : ({a, x a, x (x a)} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hea]),
      Finset.card_pair (Ne.symm hec)]
  refine le_antisymm ?_ (hcard3 ▸ Finset.card_le_card hsub)
  by_contra hlt
  push Not at hlt
  rw [← hcard3] at hlt
  obtain ⟨d, hdS, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hfd : f d = d := (Finset.mem_filter.1 hdS).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  obtain ⟨hda, hdc, hde⟩ := hd
  have hy : swap (x a) (x (x a)) * swap a (x a) ∈ N := by
    have h2 := mul_mem hx (hnorm (swap a (x a)) (hcf a (x a) hfa hfc) x⁻¹ (inv_mem hx))
    rwa [swap_inv, ← mul_assoc, ← mul_assoc, ← swap_apply_apply] at h2
  have hz := mul_mem hy (hnorm (swap (x a) d) (hcf (x a) d hfc hfd) _ hy)
  rw [swap_conj_prod (Ne.symm ha) (Ne.symm hea) (Ne.symm hda) (Ne.symm hec) (Ne.symm hdc)
    (Ne.symm hde)] at hz
  have hcomm : Commute (swap a (x a)) (swap (x (x a)) d) :=
    (disjoint_swap_swap (by simp [Ne.symm ha, Ne.symm hea, Ne.symm hda, Ne.symm hdc,
      Ne.symm hde])).commute
  have hzz : swap a (x a) * swap (x (x a)) d * (swap a (x a) * swap (x (x a)) d) = 1 := by
    calc swap a (x a) * swap (x (x a)) d * (swap a (x a) * swap (x (x a)) d)
        = swap a (x a) * (swap (x (x a)) d * swap a (x a)) * swap (x (x a)) d := by group
      _ = swap a (x a) * (swap a (x a) * swap (x (x a)) d) * swap (x (x a)) d := by
          rw [hcomm.eq]
      _ = 1 := by rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]
  have h2 : (swap a (x a) * swap (x (x a)) d) a = x a := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hea) (Ne.symm hda), swap_apply_left]
  rw [eq_one_of_mul_self hN hz hzz, Perm.one_apply] at h2
  exact ha h2.symm

end OddNormal

theorem int_dvd_card_sub_three [Fintype α] {F : Subgroup (Perm α)}
    (h3 : ∀ f ∈ F, f ≠ 1 → (Finset.univ.filter fun p => f p = p).card = 3) :
    (Nat.card F : ℤ) ∣ (Fintype.card α : ℤ) - 3 := by
  classical
  have : Fintype ↥F := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (↥F) α
  simp only [← Nat.card_eq_fintype_card] at hB
  have hfix : ∀ g : ↥F, Nat.card (MulAction.fixedBy α g) =
      (Finset.univ.filter fun p => (g : Perm α) p = p).card := by
    intro g
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  simp only [hfix] at hB
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : ↥F))] at hB
  have h1 : (Finset.univ.filter fun p => ((1 : ↥F) : Perm α) p = p).card = Fintype.card α := by
    simp
  have h2 : ∀ g ∈ Finset.univ.erase (1 : ↥F),
      (Finset.univ.filter fun p => (g : Perm α) p = p).card = 3 := fun g hg =>
    h3 g g.2 (fun h => Finset.ne_of_mem_erase hg (Subtype.ext h))
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card (α := ↥F)] at hB
  have hF1 : 1 ≤ Nat.card ↥F := Nat.card_pos
  refine ⟨(Nat.card (Quotient (MulAction.orbitRel ↥F α)) : ℤ) - 3, ?_⟩
  zify [hF1] at hB
  linear_combination hB

end S3T5An

end CFSG.GH74.Generic.BProg.B3
