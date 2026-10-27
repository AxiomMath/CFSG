module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024

open Equiv Equiv.Perm

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem perm_inv_apply_self (f : Perm Ω) (x : Ω) : f⁻¹ (f x) = x := f.symm_apply_apply x

theorem perm_apply_inv_self (f : Perm Ω) (x : Ω) : f (f⁻¹ x) = x := f.apply_symm_apply x

theorem isCycle_of_order {z : Perm Ω} {p : ℕ} (hp : p.Prime) (hz : orderOf z = p)
    (hn : Fintype.card Ω < 2 * p) : z.IsCycle := by
  rw [← hz] at hp hn
  exact isCycle_of_prime_order' hp hn

theorem card_support_eq {z : Perm Ω} {p : ℕ} (hp : p.Prime) (hz : orderOf z = p)
    (hn : Fintype.card Ω < 2 * p) : z.support.card = p := by
  rw [← (isCycle_of_order hp hz hn).orderOf, hz]

theorem fixes_of_commute {z t : Perm Ω} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hz : orderOf z = p) (hc : z.IsCycle) (hcomm : t * z = z * t) (ht : t * t = 1) {x : Ω}
    (hx : z x ≠ x) : t x = x := by
  have hcx : ∀ y, t (z y) = z (t y) := fun y => by
    have := congrArg (fun f : Perm Ω => f y) hcomm
    simpa [Perm.mul_apply] using this
  have htx : z (t x) ≠ t x := by
    intro h
    apply hx
    apply t.injective
    rw [hcx, h]
  obtain ⟨i, hi⟩ := hc.exists_pow_eq hx htx
  have hti : ∀ j : ℕ, ∀ y, t ((z ^ j) y) = (z ^ j) (t y) := by
    intro j y
    have hcm : Commute t z := hcomm
    have := congrArg (fun f : Perm Ω => f y) (hcm.pow_right j).eq
    simpa [Perm.mul_apply] using this
  have h1 : (z ^ (i + i)) x = x := by
    have e1 : (z ^ (i + i)) x = (z ^ i) ((z ^ i) x) := by rw [pow_add, Perm.mul_apply]
    rw [e1, hi, ← hti i x, hi]
    simpa [Perm.mul_apply] using congrArg (fun f : Perm Ω => f x) ht
  have hpow : z ^ (i + i) = 1 := (hc.pow_eq_one_iff' hx).2 h1
  have hdvd : p ∣ 2 * i := by
    rw [two_mul, ← hz]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hpi : p ∣ i := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
    · exact h
  have hzi : z ^ i = 1 := orderOf_dvd_iff_pow_eq_one.1 (hz ▸ hpi)
  rw [← hi, hzi, Perm.one_apply]

theorem sign_eq_one_of_pow_eq_one {g : Perm Ω} {p : ℕ} (hp : Odd p) (hg : g ^ p = 1) :
    Perm.sign g = 1 := by
  have h : Perm.sign g ^ p = 1 := by rw [← map_pow, hg, map_one]
  rcases Int.units_eq_one_or (Perm.sign g) with h1 | h1
  · exact h1
  · rw [h1, hp.neg_one_pow] at h
    exact absurd h (by decide)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024
