module

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p n : ℕ} {u : ℤ}

theorem not_dvd_of_pow_modEq_one (hp : p.Prime) (hn : 1 ≤ n)
    (h : u ^ p ≡ 1 [ZMOD (p : ℤ) ^ n]) : ¬(p : ℤ) ∣ u := by
  intro hd
  have hpow : ((p : ℤ) ^ n) ∣ u ^ p - 1 := Int.modEq_iff_dvd.mp h.symm
  have h1 : (p : ℤ) ∣ u ^ p - 1 := dvd_trans (dvd_pow_self _ (by omega : n ≠ 0)) hpow
  have h2 : (p : ℤ) ∣ u ^ p := dvd_pow hd hp.pos.ne'
  have h3 : (p : ℤ) ∣ 1 := (dvd_sub_right h2).mp h1
  have h4 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h3
  have h5 := hp.two_le
  omega

theorem modEq_one_of_pow_modEq_one (hp : p.Prime) (hn : 1 ≤ n)
    (h : u ^ p ≡ 1 [ZMOD (p : ℤ) ^ n]) : u ≡ 1 [ZMOD (p : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  have hpow : ((p : ℤ) ^ n) ∣ u ^ p - 1 := Int.modEq_iff_dvd.mp h.symm
  have hp1 : (p : ℤ) ∣ u ^ p - 1 := dvd_trans (dvd_pow_self _ (by omega : n ≠ 0)) hpow
  have h0 : ((u ^ p - 1 : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hp1
  push_cast at h0
  have hu1 : ((u : ZMod p)) = 1 := by
    rw [ZMod.pow_card ((u : ℤ) : ZMod p)] at h0
    linear_combination h0
  have h2 : ((u - 1 : ℤ) : ZMod p) = 0 := by push_cast [hu1]; ring
  exact (Int.modEq_iff_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2)).symm

theorem modEq_one_pow_max_of_pow_modEq_one (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hu : ¬(p : ℤ) ∣ u) (h : u ^ p ≡ 1 [ZMOD (p : ℤ) ^ n]) :
    u ≡ 1 [ZMOD (p : ℤ) ^ max 1 (n - 1)] := by
  have hpow : ((p : ℤ) ^ n) ∣ u ^ p - 1 := Int.modEq_iff_dvd.mp h.symm
  have hdvd1 : (p : ℤ) ∣ u - 1 :=
    Int.modEq_iff_dvd.mp (modEq_one_of_pow_modEq_one hp hn h).symm
  have hmul : emultiplicity (p : ℤ) (u ^ p - 1) = emultiplicity (p : ℤ) (u - 1) + 1 := by
    simpa [hp.emultiplicity_self] using
      Int.emultiplicity_pow_sub_pow hp (hp.odd_of_ne_two hp2) hdvd1 hu p
  have hle : (n : ℕ∞) ≤ emultiplicity (p : ℤ) (u - 1) + 1 := by
    rw [← hmul]; exact le_emultiplicity_of_pow_dvd hpow
  have h1 : (1 : ℕ∞) ≤ emultiplicity (p : ℤ) (u - 1) := by
    simpa using le_emultiplicity_of_pow_dvd (k := 1) (by simpa using hdvd1)
  have key : ((max 1 (n - 1) : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ) (u - 1) := by
    rcases eq_or_ne (emultiplicity (p : ℤ) (u - 1)) ⊤ with htop | htop
    · rw [htop]; exact le_top
    · lift emultiplicity (p : ℤ) (u - 1) to ℕ using htop with k hk
      rw [Nat.cast_le]
      rw [show ((k : ℕ∞) + 1) = ((k + 1 : ℕ) : ℕ∞) by push_cast; ring, Nat.cast_le] at hle
      rw [Nat.one_le_cast] at h1
      omega
  exact Int.modEq_iff_dvd.mpr (by simpa using (pow_dvd_of_le_emultiplicity key).neg_right)

theorem modEq_one_pow_max_of_pow_modEq_one' (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (h : u ^ p ≡ 1 [ZMOD (p : ℤ) ^ n]) : u ≡ 1 [ZMOD (p : ℤ) ^ max 1 (n - 1)] :=
  modEq_one_pow_max_of_pow_modEq_one hp hp2 hn (not_dvd_of_pow_modEq_one hp hn h) h

theorem modEq_one_pow_sub_one_of_pow_modEq_one (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (h : u ^ p ≡ 1 [ZMOD (p : ℤ) ^ n]) : u ≡ 1 [ZMOD (p : ℤ) ^ (n - 1)] := by
  have := modEq_one_pow_max_of_pow_modEq_one' hp hp2 (by omega) h
  rwa [max_eq_right (by omega : 1 ≤ n - 1)] at this

end

end CFSG.FeitThompson
