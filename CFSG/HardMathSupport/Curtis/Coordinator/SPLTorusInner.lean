module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem mem_inner_of_pow_eq_one {S : Type*} [Group S] {q : ℕ} (hq : q.Prime)
    (hOut : ¬ q ∣ Nat.card (Outer S)) {α : MulAut S} {k : ℕ} (h : α ^ q ^ k = 1) :
    α ∈ inner S := by
  have h1 : (QuotientGroup.mk α : Outer S) ^ q ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, h, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk α : Outer S) ∣ q ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk α : Outer S) ∣ Nat.card (Outer S) := orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).1 h2
  have hj0 : j = 0 := by
    by_contra hj0
    apply hOut
    rw [hj] at h3
    exact (dvd_pow_self q hj0).trans h3
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact (QuotientGroup.eq_one_iff _).1 hj

theorem conj_injective_of_center_eq_bot' {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr fun g => by
    have h := DFunLike.congr_fun ha g
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * a = a * g * a⁻¹ * a := by rw [h]
      _ = a * g := by group
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hmem

theorem five_le_of_dvd_sq_add_one {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hdvd : r ∣ p ^ 2 + 1) (hndvd : ¬ r ∣ p ^ 2 - 1) : 5 ≤ r := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  by_contra h
  have h2 := hr.two_le
  have hcases : r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hcases with rfl | rfl | rfl
  · apply hndvd
    obtain ⟨m, hm⟩ := hpodd
    subst hm
    exact ⟨2 * m * m + 2 * m, by
      have : (2 * m + 1) ^ 2 - 1 = 4 * m * m + 4 * m := by
        have h1 : (2 * m + 1) ^ 2 = 4 * m * m + 4 * m + 1 := by ring
        omega
      rw [this]; ring⟩
  · have h3 : (p ^ 2 + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases this with h0 | h0 | h0 <;> simp [Nat.add_mod, Nat.pow_mod, h0] at h3
  · exact absurd hr (by norm_num)

theorem ne_of_dvd_sq_add_one {p r : ℕ} (hp : p.Prime) (hdvd : r ∣ p ^ 2 + 1) : r ≠ p := by
  rintro rfl
  have h1 : r ∣ r ^ 2 := dvd_pow_self r two_ne_zero
  have h2 : r ∣ 1 := (Nat.dvd_add_right h1).1 hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

end CFSG.HardMathSupport.Curtis.Coordinator
