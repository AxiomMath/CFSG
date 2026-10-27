module

public import CFSG.GH74.GLS.C3.Prop121.Card7Defs

public section

namespace CFSG.Certificates.Kernel.F7Conj

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7

theorem val_mul (a b : F7) : ((a * b : F7) : Amb 7) = (a : Amb 7) * (b : Amb 7) := rfl

theorem val_inv (a : F7) : ((a⁻¹ : F7) : Amb 7) = (a : Amb 7)⁻¹ := rfl

theorem val_pow (a : F7) (k : ℕ) : ((a ^ k : F7) : Amb 7) = (a : Amb 7) ^ k :=
  Subgroup.coe_pow _ _ _

theorem sign_eq (f : F7) : sign (f : Amb 7).1 = sign (f : Amb 7).2 := f.2.2

theorem comm_x4 (f : F7) : (f : Amb 7).2 * x4 = x4 * (f : Amb 7).2 := f.2.1

theorem fst_pow (f : F7) (k : ℕ) : ((f ^ k : F7) : Amb 7).1 = (f : Amb 7).1 ^ k := by
  rw [val_pow, Prod.pow_fst]

theorem snd_pow (f : F7) (k : ℕ) : ((f ^ k : F7) : Amb 7).2 = (f : Amb 7).2 ^ k := by
  rw [val_pow, Prod.pow_snd]

theorem fst_ne_one {f : F7} (h1 : f ≠ 1) (h2 : (f : Amb 7).2 = 1) : (f : Amb 7).1 ≠ 1 := by
  intro h
  apply h1
  apply Subtype.ext
  exact Prod.ext h h2

theorem exists_conj_of_cycleType {f g : F7} (hf : (f : Amb 7).2 = 1) (hg : (g : Amb 7).2 = 1)
    (h : (f : Amb 7).1.cycleType = (g : Amb 7).1.cycleType) : ∃ k : F7, k * f * k⁻¹ = g := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 h)
  let e : Perm (Fin 4) := if sign c = 1 then 1 else swap 0 1
  have he : e * x4 = x4 * e := by
    by_cases hs : sign c = 1
    · simp [e, hs]
    · simp only [e, if_neg hs]
      decide
  have hse : sign c = sign e := by
    by_cases hs : sign c = 1
    · simp [e, hs]
    · simp only [e, if_neg hs]
      rw [sign_swap (by decide)]
      rcases Int.units_eq_one_or (sign c) with h' | h'
      · exact absurd h' hs
      · exact h'
  refine ⟨⟨(c, e), he, hse⟩, ?_⟩
  apply Subtype.ext
  rw [val_mul, val_mul, val_inv]
  refine Prod.ext ?_ ?_
  · exact hc
  · simp [hf, hg]

theorem cycleType_of_pow_prime {m p : ℕ} [hp : Fact p.Prime] {r : Perm (Fin m)} (h : r ^ p = 1)
    (h1 : r ≠ 1) : ∃ k, r.cycleType = Multiset.replicate (k + 1) p ∧ numMoved r = (k + 1) * p := by
  have ho : orderOf r = p := orderOf_eq_prime h h1
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ hp.out)
  rw [ho] at hk
  refine ⟨k, hk, ?_⟩
  rw [numMoved_eq_card_support, ← sum_cycleType, hk, Multiset.sum_replicate, smul_eq_mul]

theorem numMoved_le {m : ℕ} (r : Perm (Fin m)) : numMoved r ≤ m := by
  rw [numMoved_eq_card_support]
  exact (Finset.card_le_univ _).trans (Fintype.card_fin m).le

theorem two_le_numMoved {m : ℕ} {r : Perm (Fin m)} (h : r ≠ 1) : 2 ≤ numMoved r := by
  rw [numMoved_eq_card_support]
  have h0 : r.support.card ≠ 0 := fun h0 => h (card_support_eq_zero.1 h0)
  have h1 := card_support_ne_one (f := r)
  omega

theorem sign_of_cycleType_two {m k : ℕ} {r : Perm (Fin m)}
    (hk : r.cycleType = Multiset.replicate (k + 1) 2) : sign r = (-1) ^ (3 * (k + 1)) := by
  rw [sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  congr 1
  ring

theorem even_of_sign_one {j : ℕ} (h : ((-1 : ℤˣ) ^ j) = 1) : Even j := by
  rcases Nat.even_or_odd j with he | ho
  · exact he
  · rw [ho.neg_one_pow] at h
    exact absurd h (by decide)

theorem cycleType_of_even_inv {r : Perm (Fin 7)} (h2 : r ^ 2 = 1) (h1 : r ≠ 1) (hs : sign r = 1) :
    r.cycleType = Multiset.replicate 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hn⟩ := cycleType_of_pow_prime h2 h1
  have he := even_of_sign_one ((sign_of_cycleType_two hk).symm.trans hs)
  have hle := numMoved_le r
  obtain ⟨j, hj⟩ := he
  have hk1 : k = 1 := by omega
  rw [hk, hk1]

theorem numMoved_one {m : ℕ} : numMoved (1 : Perm (Fin m)) = 0 := by
  rw [numMoved_eq_card_support, support_one, Finset.card_empty]

theorem cycleType_of_pow_three {m j : ℕ} {r : Perm (Fin m)} (h3 : r ^ 3 = 1)
    (hn : numMoved r = 3 * j) (hj : 0 < j) : r.cycleType = Multiset.replicate j 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : r ≠ 1 := by
    rintro rfl
    rw [numMoved_one] at hn
    omega
  obtain ⟨k, hk, hm⟩ := cycleType_of_pow_prime h3 h1
  have hkj : k + 1 = j := by omega
  rw [hk, hkj]

theorem numMoved_sign_of_sq {m : ℕ} {r : Perm (Fin m)} (h2 : r ^ 2 = 1) :
    ∃ a, numMoved r = 2 * a ∧ sign r = (-1) ^ a := by
  by_cases h1 : r = 1
  · subst h1
    exact ⟨0, numMoved_one, by simp⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk, hm⟩ := cycleType_of_pow_prime h2 h1
    refine ⟨k + 1, by rw [hm]; ring, ?_⟩
    have h3 : ((-1 : ℤˣ) ^ 3) = -1 := by decide
    rw [sign_of_cycleType_two hk, pow_mul, h3]

theorem eq_one_of_numMoved {m : ℕ} {r : Perm (Fin m)} (h : numMoved r = 0) : r = 1 :=
  card_support_eq_zero.1 h

@[expose] def w5 : Perm (Fin 7) := swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6

theorem w5_comm : w5 * swap 0 1 = swap 0 1 * w5 := by decide

theorem w5_pow : w5 ^ 5 = 1 := by decide

theorem w5_ne_one : w5 ≠ 1 := by decide

theorem sign_w5 : sign w5 = 1 := by
  simp [w5, sign_mul, sign_swap]

theorem cycleType_swap01 : (swap (0 : Fin 7) 1).cycleType = Multiset.replicate 1 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hn⟩ := cycleType_of_pow_prime (p := 2) (r := swap (0 : Fin 7) 1) (by decide)
    (by decide)
  have h2 : numMoved (swap (0 : Fin 7) 1) = 2 := by decide
  have : k = 0 := by omega
  rw [hk, this]

theorem exists_comm_five {r : Perm (Fin 7)} (h2 : r ^ 2 = 1) (hn : numMoved r ≤ 2) :
    ∃ w : Perm (Fin 7), w * r = r * w ∧ sign w = 1 ∧ w ^ 5 = 1 ∧ w ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ : ∃ c : Perm (Fin 7), c * (if r = 1 then 1 else swap 0 1) * c⁻¹ = r := by
    by_cases h1 : r = 1
    · exact ⟨1, by simp [h1]⟩
    · rw [if_neg h1]
      obtain ⟨k, hk, hm⟩ := cycleType_of_pow_prime h2 h1
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      exact isConj_iff.1 (isConj_iff_cycleType_eq.2 (cycleType_swap01.trans hk.symm))
  have hw : w5 * (if r = 1 then 1 else swap 0 1) = (if r = 1 then 1 else swap 0 1) * w5 := by
    split_ifs
    · simp
    · exact w5_comm
  refine ⟨c * w5 * c⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [← hc]
    calc c * w5 * c⁻¹ * (c * (if r = 1 then 1 else swap 0 1) * c⁻¹)
        = c * (w5 * (if r = 1 then 1 else swap 0 1)) * c⁻¹ := by group
      _ = c * ((if r = 1 then 1 else swap 0 1) * w5) * c⁻¹ := by rw [hw]
      _ = c * (if r = 1 then 1 else swap 0 1) * c⁻¹ * (c * w5 * c⁻¹) := by group
  · rw [map_mul, map_mul, sign_w5, map_inv, mul_one, mul_inv_cancel]
  · rw [conj_pow, w5_pow, mul_one, mul_inv_cancel]
  · intro h
    rw [conj_eq_one_iff] at h
    exact w5_ne_one h

end CFSG.Certificates.Kernel.F7Conj

end
