module

public import CFSG.Blueprint.MultiplierDefs
public import CFSG.Open.StatedDefs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

@[expose] def tors (r x : ℕ) : ℕ := if r ∣ x then r else 1

theorem tors_of_dvd {r x : ℕ} (h : r ∣ x) : tors r x = r := by simp [tors, h]

theorem tors_of_not_dvd {r x : ℕ} (h : ¬ r ∣ x) : tors r x = 1 := by simp [tors, h]

theorem tors_le {r x : ℕ} (hr : 1 ≤ r) : tors r x ≤ r := by
  unfold tors; split_ifs <;> omega

theorem tors_eq_one_of_le {r x : ℕ} (hr : 5 ≤ r) (h0 : 0 < x) (h : x ≤ 4) : tors r x = 1 := by
  refine tors_of_not_dvd fun hd => ?_
  have := Nat.le_of_dvd h0 hd
  omega

theorem genericOrders_fst_pos {t : StatedLieTag} {n p f : ℕ} (h : StatedLieAdmissible t n p f) :
    0 < (genericOrders t n p f).1 := by
  obtain ⟨hp, hf, h⟩ := h
  cases t <;> simp only at h <;> simp only [genericOrders] <;> (try split_ifs) <;>
    first
    | exact Nat.gcd_pos_of_pos_left _ (by omega)
    | norm_num

theorem genericOrders_snd_le (t : StatedLieTag) (n p f : ℕ) :
    0 < (genericOrders t n p f).2 ∧ (genericOrders t n p f).2 ≤ 2 := by
  cases t <;> simp only [genericOrders] <;> (try split_ifs) <;> norm_num

theorem exceptionalOrders_le (t : StatedLieTag) (n p f : ℕ) :
    (0 < (exceptionalOrders t n p f).1 ∧ (exceptionalOrders t n p f).1 ≤ 4) ∧
    (0 < (exceptionalOrders t n p f).2 ∧ (exceptionalOrders t n p f).2 ≤ 4) := by
  unfold exceptionalOrders
  split <;> norm_num

@[expose] def torsBound (r : ℕ) (t : StatedLieTag) (n p f : ℕ) : ℕ :=
  tors r (genericOrders t n p f).1 * tors r (genericOrders t n p f).2 *
    (tors r (exceptionalOrders t n p f).1 * tors r (exceptionalOrders t n p f).2)

theorem torsBound_le_of_five_le {r : ℕ} (hr : 5 ≤ r) (t : StatedLieTag) (n p f : ℕ) :
    torsBound r t n p f ≤ r := by
  have hb := tors_eq_one_of_le hr (genericOrders_snd_le t n p f).1
    (le_trans (genericOrders_snd_le t n p f).2 (by norm_num))
  have hc := tors_eq_one_of_le hr (exceptionalOrders_le t n p f).1.1
    (exceptionalOrders_le t n p f).1.2
  have hd := tors_eq_one_of_le hr (exceptionalOrders_le t n p f).2.1
    (exceptionalOrders_le t n p f).2.2
  have ha := tors_le (r := r) (x := (genericOrders t n p f).1) (by omega)
  unfold torsBound
  rw [hb, hc, hd]
  simpa using ha

theorem eq_psu_four_three_of_nine_le {t : StatedLieTag} {n p f : ℕ}
    (h9 : 9 ≤ torsBound 3 t n p f) : t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1 := by
  have hb : tors 3 (genericOrders t n p f).2 = 1 := by
    obtain ⟨h1, h2⟩ := genericOrders_snd_le t n p f
    exact tors_of_not_dvd fun hd => by have := Nat.le_of_dvd h1 hd; omega
  have ha := tors_le (r := 3) (x := (genericOrders t n p f).1) (by norm_num)
  unfold torsBound at h9
  rw [hb] at h9
  revert h9
  unfold exceptionalOrders
  split
  all_goals intro h
  all_goals simp only [tors] at h ha
  all_goals first
    | exact ⟨rfl, rfl, rfl, rfl⟩
    | (exfalso; revert h; simp [genericOrders]; done)
    | (exfalso; simp only [Nat.dvd_one, OfNat.ofNat_ne_one, ite_false] at h
       split_ifs at h ha <;> omega)


theorem genericOrders_fst_le_four {t : StatedLieTag} (h1 : t ≠ .PSL) (h2 : t ≠ .PSU)
    (n p f : ℕ) : (genericOrders t n p f).1 ≤ 4 := by
  cases t <;> simp only [genericOrders] <;> (try split_ifs) <;>
    first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | exact (Nat.gcd_le_left _ (by norm_num)).trans (by norm_num)
    | norm_num

set_option linter.unusedTactic false in
theorem not_three_dvd_exceptional_of_dvd_generic {t : StatedLieTag} {n p f : ℕ}
    (h : 3 ∣ (genericOrders t n p f).1) :
    ¬ 3 ∣ (exceptionalOrders t n p f).1 ∧ ¬ 3 ∣ (exceptionalOrders t n p f).2 := by
  revert h
  unfold exceptionalOrders
  split
  all_goals intro h
  all_goals first
    | (norm_num; done)
    | (exfalso; revert h; simp [genericOrders]; done)

theorem card_pow_zmod_le {m r : ℕ} (hr : r.Prime) (hm : 0 < m) :
    Nat.card {y : Multiplicative (ZMod m) // y ^ r = 1} ≤ tors r m := by
  have : NeZero m := ⟨hm.ne'⟩
  by_cases hd : r ∣ m
  · rw [tors_of_dvd hd]
    classical
    have h := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod m)) (n := r) hr.pos
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h
  · rw [tors_of_not_dvd hd]
    have key : ∀ z : {y : Multiplicative (ZMod m) // y ^ r = 1}, z.1 = 1 := fun z => by
      have h1 : orderOf z.1 ∣ r := orderOf_dvd_of_pow_eq_one z.2
      have h2 : orderOf z.1 ∣ m := by
        have := orderOf_dvd_natCard z.1
        rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at this
      have hcop : Nat.Coprime r m := (Nat.Prime.coprime_iff_not_dvd hr).2 hd
      have h3 : orderOf z.1 ∣ Nat.gcd r m := Nat.dvd_gcd h1 h2
      rw [hcop.gcd_eq_one] at h3
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    have : Subsingleton {y : Multiplicative (ZMod m) // y ^ r = 1} :=
      ⟨fun x y => Subtype.ext ((key x).trans (key y).symm)⟩
    exact Finite.card_le_one_iff_subsingleton.mpr this

theorem card_pow_prod {A B : Type*} [Group A] [Group B] (n : ℕ) :
    Nat.card {x : A × B // x ^ n = 1} =
      Nat.card {a : A // a ^ n = 1} * Nat.card {b : B // b ^ n = 1} := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans Equiv.subtypeProdEquivProd)
  rw [Prod.ext_iff]
  simp

theorem pow_eq_one_of_dvd_zmod {x N : ℕ} (h : x ∣ N) (y : Multiplicative (ZMod x)) :
    y ^ N = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul]
  have : y ^ x = 1 := by
    rw [← ofAdd_toAdd y, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
  rw [this, one_pow]

theorem card_pow_four_le {a b c d r : ℕ} (hr : r.Prime) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    Nat.card {x : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)) // x ^ r = 1} ≤
      tors r a * tors r b * (tors r c * tors r d) := by
  rw [card_pow_prod, card_pow_prod, card_pow_prod]
  exact Nat.mul_le_mul (Nat.mul_le_mul (card_pow_zmod_le hr ha) (card_pow_zmod_le hr hb))
    (Nat.mul_le_mul (card_pow_zmod_le hr hc) (card_pow_zmod_le hr hd))

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
