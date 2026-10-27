module

public import Mathlib.NumberTheory.LucasLehmer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

theorem tw_two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem tw_not_dvd_sign_pow {p q e k : ℕ} {s : ℤ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf (q : ZMod p) = e) (h : (s = -1 ∧ e ∣ k) ∨ (s = 1 ∧ ¬ e ∣ k)) :
    ¬ (p : ℤ) ∣ s * (q : ℤ) ^ k - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hd
  have hz : ((s * (q : ℤ) ^ k - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
  push_cast at hz
  rcases h with ⟨rfl, hek⟩ | ⟨rfl, hek⟩
  · have hqk : (q : ZMod p) ^ k = 1 := by
      obtain ⟨m, rfl⟩ := hek
      have hqe : (q : ZMod p) ^ e = 1 := by
        rw [← he]
        exact pow_orderOf_eq_one _
      rw [pow_mul, hqe, one_pow]
    push_cast at hz
    rw [hqk] at hz
    apply tw_two_ne_zero_zmod hp hp2
    linear_combination -hz
  · have hqk : (q : ZMod p) ^ k = 1 := by
      push_cast at hz
      exact sub_eq_zero.1 (by simpa using hz)
    exact hek (he ▸ orderOf_dvd_of_pow_eq_one hqk)

theorem tw_dvd_sub_of_orderOf_one {p q : ℕ} (hp : p.Prime) (he : orderOf (q : ZMod p) = 1) :
    (p : ℤ) ∣ (q : ℤ) - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  exact orderOf_eq_one_iff.1 he

theorem tw_dvd_add_of_orderOf_two {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf (q : ZMod p) = 2) : (p : ℤ) ∣ (q : ℤ) - (-1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have h2 : (q : ZMod p) ^ 2 = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one _
  have h1 : (q : ZMod p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at he
    omega
  have : ((q : ZMod p) - 1) * ((q : ZMod p) + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · linear_combination h

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
