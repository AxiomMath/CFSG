module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem cyc_three {R : Type*} [Group R] [Finite R] [IsCyclic R] {x y : R} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) : x = 1 ∨ ∃ j : ℕ, y * x ^ j = 1 := by
  classical
  have := Fintype.ofFinite R
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  right
  have hx2 : x ^ 2 ≠ 1 := fun h => hx1 (by
    have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
    rw [this, hx, h]; simp)
  have hxx : x ≠ x ^ 2 := fun h => hx1 (by
    have h3 : x * 1 = x * x := by rw [mul_one, ← pow_two]; exact h
    exact (mul_left_cancel h3).symm)
  set S : Finset R := Finset.univ.filter (fun a => a ^ 3 = 1) with hS
  have hcard : S.card ≤ 3 := by
    rw [hS]
    obtain ⟨g, hg⟩ := exists_zpow_surjective R
    -- every element of `R` is a power of the generator `g` with small exponent
    have hgen : ∀ a : R, ∃ i : ℕ, i < orderOf g ∧ g ^ i = a := by
      intro a
      obtain ⟨k, hk⟩ := hg a
      have hm : a ∈ Subgroup.zpowers g := Subgroup.mem_zpowers_iff.mpr ⟨k, hk⟩
      obtain ⟨i, hi, hii⟩ := Finset.mem_image.mp
        ((isOfFinOrder_of_finite g).mem_zpowers_iff_mem_range_orderOf.mp hm)
      exact ⟨i, Finset.mem_range.mp hi, hii⟩
    have ho0 : 0 < orderOf g := orderOf_pos_iff.mpr (isOfFinOrder_of_finite g)
    -- arithmetic: any exponent killed by `3` is a multiple of `orderOf g / gcd (orderOf g) 3`
    have hvm : ∀ i : ℕ, orderOf g ∣ 3 * i → orderOf g / Nat.gcd (orderOf g) 3 ∣ i := by
      intro i hi
      have hg0 : 0 < Nat.gcd (orderOf g) 3 := Nat.gcd_pos_of_pos_left 3 ho0
      have hcop : (orderOf g / Nat.gcd (orderOf g) 3).Coprime (3 / Nat.gcd (orderOf g) 3) :=
        Nat.coprime_div_gcd_div_gcd hg0
      have h3 : Nat.gcd (orderOf g) 3 * (3 / Nat.gcd (orderOf g) 3) = 3 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right (orderOf g) 3)
      have ho : Nat.gcd (orderOf g) 3 * (orderOf g / Nat.gcd (orderOf g) 3) = orderOf g :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left (orderOf g) 3)
      have hdiv : orderOf g / Nat.gcd (orderOf g) 3 ∣ 3 / Nat.gcd (orderOf g) 3 * i := by
        refine Nat.dvd_of_mul_dvd_mul_left hg0 ?_
        rw [ho, ← mul_assoc, h3]
        exact hi
      exact hcop.dvd_of_dvd_mul_left hdiv
    set v : R := g ^ (orderOf g / Nat.gcd (orderOf g) 3) with hv
    have hov : orderOf v ≤ 3 := by
      rw [hv, orderOf_pow]
      have hdvd : Nat.gcd (orderOf g) 3 ∣ orderOf g := Nat.gcd_dvd_left _ _
      have hge : Nat.gcd (orderOf g) (orderOf g / Nat.gcd (orderOf g) 3) =
          orderOf g / Nat.gcd (orderOf g) 3 :=
        Nat.gcd_eq_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (orderOf g) 3))
      rw [hge, Nat.div_div_self hdvd (ne_of_gt ho0)]
      exact Nat.gcd_le_right (orderOf g) (by norm_num)
    have hsub : ∀ a : R, a ^ 3 = 1 → a ∈ Subgroup.zpowers v := by
      intro a ha3
      obtain ⟨i, -, hi⟩ := hgen a
      have h3i : g ^ (3 * i) = 1 := by rw [mul_comm 3 i, pow_mul, hi, ha3]
      have hoi : orderOf g ∣ 3 * i := orderOf_dvd_iff_pow_eq_one.mpr h3i
      obtain ⟨t, ht⟩ := hvm i hoi
      have hai : a = v ^ t := by rw [← hi, ht, hv, ← pow_mul]
      rw [hai]
      exact Subgroup.npow_mem_zpowers v t
    have hfin : (Finset.univ.filter (fun a : R => a ^ 3 = 1)).card ≤
        (Finset.image (fun i => v ^ i) (Finset.range (orderOf v))).card :=
      Finset.card_le_card fun a ha => by
        rw [Finset.mem_filter] at ha
        exact (isOfFinOrder_of_finite v).mem_zpowers_iff_mem_range_orderOf.mp (hsub a ha.2)
    calc (Finset.univ.filter (fun a : R => a ^ 3 = 1)).card
        ≤ (Finset.image (fun i => v ^ i) (Finset.range (orderOf v))).card := hfin
      _ ≤ (Finset.range (orderOf v)).card := Finset.card_image_le
      _ = orderOf v := Finset.card_range (orderOf v)
      _ ≤ 3 := hov
  have hsub : ({1, x, x ^ 2} : Finset R) ⊆ S := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | rfl | rfl
    · simp
    · exact hx
    · rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
  have hc3 : ({1, x, x ^ 2} : Finset R).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hxx
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hx1 h.symm, fun h => hx2 h.symm⟩
  have heq : ({1, x, x ^ 2} : Finset R) = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hc3]; exact hcard)
  have hyS : y ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hy⟩
  rw [← heq] at hyS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyS
  rcases hyS with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨2, by rw [← pow_succ']; exact hx⟩
  · exact ⟨1, by rw [pow_one, ← pow_succ]; exact hx⟩

end CFSG.HardMathSupport.Solomon.Coordinator
