module

public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

section Vector

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

private theorem one_add_pow_two_pow (X : Module.End (ZMod 2) V) (k : ℕ) :
    (1 + X) ^ (2 ^ k) = 1 + X ^ (2 ^ k) := by
  have hdbl : ∀ Y : Module.End (ZMod 2) V, Y + Y = 0 := fun Y => LinearMap.ext fun x => by
    have h : ∀ w : V, w + w = 0 := fun w => by
      rw [← two_smul (ZMod 2) w]
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_smul]
    simp [h]
  have hsq : ∀ Y : Module.End (ZMod 2) V, (1 + Y) ^ 2 = 1 + Y ^ 2 := fun Y => by
    calc (1 + Y) ^ 2 = 1 + (Y + Y) + Y ^ 2 := by noncomm_ring
      _ = 1 + Y ^ 2 := by rw [hdbl, add_zero]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, hsq, ← pow_mul, ← pow_succ]

theorem pow_two_pow_eq_one_of_finrank_le {m k : ℕ} (hV : Module.finrank (ZMod 2) V ≤ 2 ^ m)
    (a : V ≃ₗ[ZMod 2] V) (ha : a ^ 2 ^ k = 1) : a ^ 2 ^ m = 1 := by
  let G : Module.End (ZMod 2) V := (a : V →ₗ[ZMod 2] V)
  have hpow : ∀ j : ℕ, ((a ^ j : V ≃ₗ[ZMod 2] V) : Module.End (ZMod 2) V) = G ^ j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, pow_succ, ← ih]; rfl
  let N : Module.End (ZMod 2) V := G - 1
  have hGN : G = 1 + N := by simp [N]
  have hNk : N ^ 2 ^ k = 0 := by
    have h1 : G ^ 2 ^ k = 1 := by rw [← hpow, ha]; rfl
    have h3 := one_add_pow_two_pow N k
    rw [← hGN, h1] at h3
    exact (add_left_cancel (a := (1 : Module.End (ZMod 2) V)) (by simpa using h3.symm))
  have hnil : IsNilpotent N := ⟨2 ^ k, hNk⟩
  have hNn : N ^ Module.finrank (ZMod 2) V = 0 := by
    have h1 := hnil.charpoly_eq_X_pow_finrank
    have h2 := LinearMap.aeval_self_charpoly N
    rw [h1] at h2
    simpa using h2
  have hNm : N ^ 2 ^ m = 0 := pow_eq_zero_of_le hV hNn
  have hGm : G ^ 2 ^ m = 1 := by
    have h3 := one_add_pow_two_pow N m
    rw [← hGN, hNm, add_zero] at h3
    exact h3
  refine LinearEquiv.ext fun x => ?_
  have := congrArg (fun T : Module.End (ZMod 2) V => T x) (hpow (2 ^ m))
  simp only [hGm] at this
  exact this

theorem pow_eight_eq_one_of_finrank_le {k : ℕ} (hV : Module.finrank (ZMod 2) V ≤ 8)
    (a : V ≃ₗ[ZMod 2] V) (ha : a ^ 2 ^ k = 1) : a ^ 8 = 1 :=
  pow_two_pow_eq_one_of_finrank_le (m := 3) (by simpa using hV) a ha

end Vector

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
