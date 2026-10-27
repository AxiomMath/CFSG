module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Models Equiv

set_option maxRecDepth 100000

@[expose] def tAddI : Perm (Fin 10) := perm10 [[0, 3, 6], [1, 4, 7], [2, 5, 8]]

@[expose] def tau (ab : Fin 3 × Fin 3) : Perm (Fin 10) := tAdd ^ (ab.1 : ℕ) * tAddI ^ (ab.2 : ℕ)

theorem tau_pow_nine : ∀ ab, tau ab ^ 9 = 1 := by decide +kernel

theorem tau_fix_nine : ∀ ab, tau ab 9 = 9 := by decide +kernel

theorem tau_comm : ∀ ab cd, tau ab * tau cd = tau cd * tau ab := by decide +kernel

theorem tau_reach : ∀ k : Fin 10, k ≠ 9 → ∃ ab, tau ab 0 = k := by decide +kernel

theorem tau_inj : ∀ ab cd, tau ab = tau cd → ab = cd := by decide +kernel

theorem tau_mul : ∀ ab cd, ∃ ef, tau ab * tau cd = tau ef := by decide +kernel

theorem tau_inv : ∀ ab, ∃ cd, (tau ab)⁻¹ = tau cd := by decide +kernel

theorem tau_one : ∃ ab, (1 : Perm (Fin 10)) = tau ab := by decide +kernel

theorem tAdd_eq_tau : tAdd = tau (1, 0) := by decide +kernel

theorem tAddI_eq_tau : tAddI = tau (0, 1) := by decide +kernel

theorem commute_tau {g : Perm (Fin 10)} (h1 : Commute g tAdd) (h2 : Commute g tAddI)
    (ab : Fin 3 × Fin 3) : Commute g (tau ab) :=
  (h1.pow_right _).mul_right (h2.pow_right _)

theorem tAdd_fix : ∀ x : Fin 10, tAdd x = x → x = 9 := by decide +kernel

theorem exists_tau_of_commute {g : Perm (Fin 10)} (h1 : Commute g tAdd) (h2 : Commute g tAddI) :
    ∃ ab, g = tau ab := by
  have h9 : g 9 = 9 := by
    apply tAdd_fix
    have := congrArg (fun f : Perm (Fin 10) => f 9) h1.eq
    simp only [Perm.mul_apply] at this
    have h : tAdd 9 = 9 := by decide +kernel
    rw [h] at this
    exact this.symm
  have h0 : g 0 ≠ 9 := fun h => by
    have := g.injective (h.trans h9.symm)
    exact absurd this (by decide)
  obtain ⟨t, ht0⟩ := tau_reach (g 0) h0
  refine ⟨t, ?_⟩
  ext x
  by_cases hx : x = 9
  · subst hx
    rw [h9, tau_fix_nine t]
  · obtain ⟨s, rfl⟩ := tau_reach x hx
    have h := congrArg (fun f : Perm (Fin 10) => f 0) (commute_tau h1 h2 s).eq
    simp only [Perm.mul_apply] at h
    have h' := congrArg (fun f : Perm (Fin 10) => f 0) (tau_comm s t)
    simp only [Perm.mul_apply] at h'
    rw [h, ← ht0, h']

end CFSG.HardMathSupport.Solomon.Coordinator
