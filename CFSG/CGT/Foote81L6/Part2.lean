module

public import CFSG.CGT.Foote81L6.Rigid
public import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.CGT.Foote81L6

theorem fin3_perm {N : ℕ} (hN : Odd N) (σ : Equiv.Perm (Fin 3)) (h1 : σ ≠ 1) (hσN : σ ^ N = 1) :
    σ ^ 3 = 1 ∧ ∀ i j : Fin 3, ∃ m : ℕ, (σ ^ m) i = j := by
  have aux : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ ^ 2 ≠ 1 →
      σ ^ 3 = 1 ∧ ∀ i j : Fin 3, ∃ m : ℕ, m < 3 ∧ (σ ^ m) i = j := by decide
  have h2 : σ ^ 2 ≠ 1 := by
    intro h2
    apply h1
    obtain ⟨k, rfl⟩ := hN
    rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hσN
    exact hσN
  obtain ⟨h3, h4⟩ := aux σ h1 h2
  exact ⟨h3, fun i j => by obtain ⟨m, -, hm⟩ := h4 i j; exact ⟨m, hm⟩⟩

theorem part2 (a : Fin 3 → ℕ) (ha : ∀ i, 2 ≤ a i) (y : MulAut (PX a)) (hy : y ≠ 1) {N : ℕ}
    (hN : Odd N) (hyN : y ^ N = 1) :
    (∀ i j, a i = a j) ∧ orderOf y = 3 ∧
      ∃ σ : Equiv.Perm (Fin 3), (∀ j, y (zz a j) = zz a (σ j)) ∧
        ∀ i j, ∃ m : ℕ, (σ ^ m) i = j := by
  obtain ⟨σ, hσ, hle⟩ := perm ha y
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hy
    refine eq_one_of_fix ha y hN hyN fun j => ?_
    rw [hσ, h]; rfl
  have hσN : σ ^ N = 1 := by
    refine Equiv.ext fun j => ?_
    have h1 := pow_zz y σ hσ N j
    rw [hyN, MulAut.one_apply] at h1
    exact (zz_injective (by have := ha j; omega) (by have := ha ((σ ^ N) j); omega) h1).symm
  obtain ⟨h3, htr⟩ := fin3_perm hN σ hσ1 hσN
  have hmono : ∀ m i, a i ≤ a ((σ ^ m) i) := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact (hle i).trans (ih (σ i))
  have haeq : ∀ i j, a i = a j := by
    intro i j
    obtain ⟨m, hm⟩ := htr i j
    obtain ⟨m', hm'⟩ := htr j i
    exact le_antisymm (hm ▸ hmono m i) (hm' ▸ hmono m' j)
  have hy3 : y ^ 3 = 1 := by
    refine eq_one_of_fix ha (y ^ 3) hN (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow])
      fun j => ?_
    rw [pow_zz y σ hσ 3 j, h3]; rfl
  have hord : orderOf y = 3 := by
    have hd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy
    · exact h
  exact ⟨haeq, hord, σ, hσ, htr⟩

end CFSG.CGT.Foote81L6
