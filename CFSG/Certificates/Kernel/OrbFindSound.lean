module

public import Certificates.Data.Kernel.OrbFind
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.KC.OrbFind

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.BfsPin

variable {n w : Nat}

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem memK_spec {ps : List Nat} {N : Nat} {T S : Nat → Nat} {v : Nat}
    (h : memK n w ps N T S v = true) : ∃ j < N, T j = v := by
  unfold memK at h
  rw [strictB_eq', bAnd_eq, Bool.and_eq_true] at h
  exact ⟨_, Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem isIdK_iff {P : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g) :
    isIdK n w P = true ↔ g = 1 := by
  unfold isIdK
  rw [allN_iff]
  constructor
  · intro h
    refine Equiv.ext fun x => Fin.ext ?_
    have := Nat.eq_of_beq_eq_true (h x x.2)
    rw [hP x] at this
    simpa using this
  · rintro rfl i hi
    have h1 : pg w (mask w) P i = i := hP ⟨i, hi⟩
    rw [h1]
    exact Nat.beq_refl i

theorem pow_three' {G : Type*} [Monoid G] (g : G) : g * (g * g) = g ^ 3 := by
  rw [pow_succ, sq, mul_assoc]

theorem pow_four' {G : Type*} [Monoid G] (g : G) : g * g * (g * g) = g ^ 4 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]

theorem pow_five' {G : Type*} [Monoid G] (g : G) : g * (g * g * (g * g)) = g ^ 5 := by
  rw [show (5 : ℕ) = 1 + 2 + 2 from rfl, pow_add, pow_add, pow_one, sq]
  simp only [mul_assoc]

theorem pow_eight' {G : Type*} [Monoid G] (g : G) :
    g * g * (g * g) * (g * g * (g * g)) = g ^ 8 := by
  rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, ← pow_four']

theorem isInvK_iff (hn : n < 2 ^ 32) {P : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g) :
    isInvK n w P = true ↔ orderOf g = 2 := by
  unfold isInvK
  rw [bAnd_eq, Bool.and_eq_true, isIdK_iff (prep_pcomp hn hP hP), Bool.not_eq_true',
    Bool.eq_false_iff, Ne, isIdK_iff hP, ← sq]
  exact (orderOf_eq_prime_iff (p := 2)).symm

theorem ord8K_iff (hn : n < 2 ^ 32) {P : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g) :
    ord8K n w P = true ↔ orderOf g = 8 := by
  unfold ord8K
  have h2 := prep_pcomp hn hP hP
  have h4 := prep_pcomp hn h2 h2
  have h8 := prep_pcomp hn h4 h4
  rw [strictB_eq', strictB_eq', bAnd_eq, Bool.and_eq_true, isIdK_iff h8, Bool.not_eq_true',
    Bool.eq_false_iff, Ne, isIdK_iff h4]
  rw [pow_eight', pow_four']
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨h8, h4⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using h4) (by simpa using h8)
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one g, fun h4 => ?_⟩
    have := orderOf_dvd_of_pow_eq_one h4
    rw [h] at this
    norm_num at this

theorem ord5K_spec (hn : n < 2 ^ 32) {P : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g)
    (h : ord5K n w P = true) : g ^ 5 = 1 ∧ g ≠ 1 := by
  unfold ord5K at h
  have h2 := prep_pcomp hn hP hP
  rw [strictB_eq', bAnd_eq, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Ne,
    isIdK_iff hP, isIdK_iff (prep_pcomp hn hP (prep_pcomp hn h2 h2))] at h
  refine ⟨?_, h.1⟩
  rw [← pow_five', h.2]

theorem oddK_spec (hn : n < 2 ^ 32) {P : Nat} {g : Equiv.Perm (Fin n)} (hP : PRep n w P g)
    (h : oddK n w P = true) : Odd (orderOf g) := by
  unfold oddK at h
  have h2 := prep_pcomp hn hP hP
  rw [strictB_eq', bAnd_eq, Bool.and_eq_true, Bool.or_eq_true, isIdK_iff (prep_pcomp hn hP h2),
    isIdK_iff (prep_pcomp hn hP (prep_pcomp hn h2 h2))] at h
  rcases h.2 with h3 | h5
  · have e : g ^ 3 = 1 := by rw [← pow_three', h3]
    have := orderOf_dvd_of_pow_eq_one e
    exact Odd.of_dvd_nat (by decide) this
  · have e : g ^ 5 = 1 := by rw [← pow_five', h5]
    have := orderOf_dvd_of_pow_eq_one e
    exact Odd.of_dvd_nat (by decide) this

end CFSG.KC.OrbFind

end
