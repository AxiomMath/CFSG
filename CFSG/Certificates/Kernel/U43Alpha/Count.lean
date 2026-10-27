module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.KS.U43Alpha

open Finset

variable {N : ℕ} {f : ℕ → ℕ} {lab : ℕ → ℕ}

@[expose] def cls (N : ℕ) (lab : ℕ → ℕ) (i : ℕ) : Finset ℕ := (range N).filter fun q => lab q = i

theorem mem_cls {y i : ℕ} : y ∈ cls N lab i ↔ y < N ∧ lab y = i := by
  unfold cls
  rw [Finset.mem_filter, Finset.mem_range]

@[expose] def fixS (N : ℕ) (f : ℕ → ℕ) : Finset ℕ := (range N).filter fun q => f q = q

theorem two_dvd_card_sub_fix {X : Finset ℕ} (hX : ∀ x ∈ X, f x ∈ X) (hff : ∀ x ∈ X, f (f x) = x) :
    2 ∣ X.card - (X.filter fun x => f x = x).card ∧ (X.filter fun x => f x = x).card ≤ X.card := by
  refine ⟨?_, card_filter_le _ _⟩
  have hsplit := card_filter_add_card_filter_not (s := X) (fun x => f x = x)
  have hne : (X.filter fun x => ¬ f x = x) = (X.filter fun x => x < f x) ∪ (X.filter fun x => f x < x) := by
    ext x
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hx, h⟩
      rcases Nat.lt_or_gt_of_ne (Ne.symm h) with h' | h'
      · exact Or.inl ⟨hx, h'⟩
      · exact Or.inr ⟨hx, h'⟩
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · exact ⟨hx, by omega⟩
      · exact ⟨hx, by omega⟩
  have hdis : Disjoint (X.filter fun x => x < f x) (X.filter fun x => f x < x) := by
    rw [disjoint_filter]
    intro x _ h1 h2
    omega
  have hPQ : (X.filter fun x => x < f x).card = (X.filter fun x => f x < x).card := by
    refine card_bij' (fun a _ => f a) (fun a _ => f a) ?_ ?_ ?_ ?_
    · intro a ha
      rw [mem_filter] at ha ⊢
      exact ⟨hX a ha.1, by rw [hff a ha.1]; exact ha.2⟩
    · intro a ha
      rw [mem_filter] at ha ⊢
      exact ⟨hX a ha.1, by rw [hff a ha.1]; exact ha.2⟩
    · intro a ha
      exact hff a (mem_filter.1 ha).1
    · intro a ha
      exact hff a (mem_filter.1 ha).1
  rw [hne, card_union_of_disjoint hdis, hPQ] at hsplit
  exact ⟨(X.filter fun x => f x < x).card, by omega⟩

section Labels

variable (hf : ∀ x < N, f x < N) (hff : ∀ x < N, f (f x) = x)
  (hfix : ∀ x < N, ∀ y < N, lab x = lab y → f x = x → f y = y)
  (hlab : ∀ x < N, ∀ y < N, lab x = lab y → lab (f x) = lab (f y))
include hf hff hlab

theorem card_cls_f {x : ℕ} (hx : x < N) : (cls N lab (lab (f x))).card = (cls N lab (lab x)).card := by
  have key : ∀ y < N, (cls N lab (lab y)).card ≤ (cls N lab (lab (f y))).card := by
    intro y hy
    refine card_le_card_of_injOn f (fun z hz => ?_) (fun a ha b hb e => ?_)
    · simp only [cls, coe_filter, Set.mem_setOf_eq, mem_range] at hz ⊢
      exact ⟨hf z hz.1, hlab z hz.1 y hy hz.2⟩
    · simp only [cls, coe_filter, Set.mem_setOf_eq, mem_range] at ha hb
      rw [← hff a ha.1, ← hff b hb.1, e]
  have h1 := key x hx
  have h2 := key (f x) (hf x hx)
  rw [hff x hx] at h2
  omega

omit hlab in
include hfix in
theorem card_fix_eq_sum :
    (fixS N f).card = ∑ i ∈ (fixS N f).image lab, (cls N lab i).card := by
  rw [card_eq_sum_card_image lab]
  refine sum_congr rfl fun i hi => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
  simp only [fixS, mem_filter, mem_range] at hx
  congr 1
  ext y
  simp only [fixS, cls, mem_filter, mem_range]
  constructor
  · rintro ⟨⟨hy, -⟩, e⟩
    exact ⟨hy, e⟩
  · rintro ⟨hy, e⟩
    exact ⟨⟨hy, hfix x hx.1 y hy e.symm hx.2⟩, e⟩

include hfix in
theorem le_card_fix_size {nb s : ℕ} (hnb : ∀ x < N, lab x < nb) (hs : Odd s)
    (hc : Odd ((range nb).filter fun i => (cls N lab i).card = s).card) :
    s ≤ ((fixS N f).filter fun x => (cls N lab (lab x)).card = s).card := by
  set X := (range N).filter fun x => (cls N lab (lab x)).card = s with hXdef
  set I := (range nb).filter fun i => (cls N lab i).card = s with hIdef
  have hXsub : ∀ x ∈ X, x < N := fun x hx => mem_range.1 (mem_filter.1 hx).1
  have hX : X.card = s * I.card := by
    rw [card_eq_sum_card_fiberwise (f := lab) (t := I) (fun x hx => ?_)]
    · rw [sum_const_nat (m := s) fun i hi => ?_, mul_comm]
      obtain ⟨-, hi2⟩ := Finset.mem_filter.1 hi
      rw [← hi2]
      congr 1
      ext y
      rw [mem_cls, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hy, -⟩, e⟩
        exact ⟨Finset.mem_range.1 hy, e⟩
      · rintro ⟨hy, e⟩
        exact ⟨⟨Finset.mem_range.2 hy, by rw [e]; exact hi2⟩, e⟩
    · obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hnb x (Finset.mem_range.1 hx1)), hx2⟩
  have hF : (X.filter fun x => f x = x) = (fixS N f).filter fun x => (cls N lab (lab x)).card = s := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, fixS, Finset.mem_filter]
    tauto
  have hFs : (X.filter fun x => f x = x).card = s * ((X.filter fun x => f x = x).image lab).card := by
    rw [card_eq_sum_card_image lab, sum_const_nat (m := s) fun i hi => ?_, mul_comm]
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨hxX, hfx⟩ := Finset.mem_filter.1 hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hxX
    have hxN := Finset.mem_range.1 hx1
    rw [← hx2]
    congr 1
    ext y
    rw [mem_cls, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨hy, -⟩, -⟩, e⟩
      exact ⟨Finset.mem_range.1 hy, e⟩
    · rintro ⟨hy, e⟩
      exact ⟨⟨⟨Finset.mem_range.2 hy, by rw [e]; exact hx2⟩, hfix x hxN y hy e.symm hfx⟩, e⟩
  have hinv : ∀ x ∈ X, f x ∈ X := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    have hxN := Finset.mem_range.1 hx1
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hf x hxN), by rw [card_cls_f hf hff hlab hxN]; exact hx2⟩
  obtain ⟨hpar, hle⟩ := two_dvd_card_sub_fix hinv fun x hx => hff x (hXsub x hx)
  rw [← hF]
  set m := ((X.filter fun x => f x = x).image lab).card
  rw [hFs] at hpar hle ⊢
  rw [hX] at hpar hle
  have hs' : s % 2 = 1 := Nat.odd_iff.1 hs
  have hc' : I.card % 2 = 1 := Nat.odd_iff.1 hc
  have hm : m ≤ I.card := Nat.le_of_mul_le_mul_left hle (by omega)
  have hsub : s * I.card - s * m = s * (I.card - m) := (Nat.mul_sub s I.card m).symm
  rw [hsub] at hpar
  have hmod : (s * (I.card - m)) % 2 = (I.card - m) % 2 := by
    rw [Nat.mul_mod, hs', one_mul, Nat.mod_mod]
  obtain ⟨c, hc2⟩ := hpar
  generalize s * (I.card - m) = P at hc2 hmod
  have hm1 : 1 ≤ m := by omega
  calc s = s * 1 := (mul_one s).symm
    _ ≤ s * m := Nat.mul_le_mul_left s hm1

end Labels

end CFSG.KS.U43Alpha

end
