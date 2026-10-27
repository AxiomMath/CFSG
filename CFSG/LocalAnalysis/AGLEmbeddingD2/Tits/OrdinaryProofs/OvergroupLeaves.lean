module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.OvergroupLeaves

section GL2

theorem add_self_eq_zero_matrix {F : Type} [Field F] [CharP F 2]
    (A : Matrix (Fin 2) (Fin 2) F) : A + A = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem add_one_pow_two_pow {F : Type} [Field F] [CharP F 2] (A : Matrix (Fin 2) (Fin 2) F)
    (n : ℕ) : (A + 1) ^ (2 ^ n) = A ^ (2 ^ n) + 1 := by
  have sq_step : ∀ a : Matrix (Fin 2) (Fin 2) F, (a + 1) ^ 2 = a ^ 2 + 1 := by
    intro a
    rw [sq, sq, show (a + 1) * (a + 1) = a * a + (a + a) + 1 by noncomm_ring,
      add_self_eq_zero_matrix, add_zero]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ 2 n, pow_mul, pow_mul, ih, sq_step]

theorem mul_self_eq_zero_of_pow_succ_eq_zero {F : Type} [Field F] (N : Matrix (Fin 2) (Fin 2) F)
    {m : ℕ} (hm : N ^ (m + 1) = 0) : N * N = 0 := by
  set t : F := N 0 0 + N 1 1 with ht_def
  have hCH : N * N = t • N - (N 0 0 * N 1 1 - N 0 1 * N 1 0) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht_def] <;> ring
  have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 0 := by
    have h := congrArg Matrix.det hm
    rw [Matrix.det_pow, Matrix.det_zero] at h
    have hd : N.det = 0 := (pow_eq_zero_iff (Nat.succ_ne_zero m)).1 h
    rw [Matrix.det_fin_two] at hd
    exact hd
  have hsq : N * N = t • N := by
    rw [hCH, hdet, zero_smul, sub_zero]
  have hpow : ∀ j : ℕ, N ^ (j + 1) = (t ^ j) • N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih, smul_mul_assoc, hsq, smul_smul, ← pow_succ]
  rw [hpow m] at hm
  by_cases ht : t = 0
  · rw [hsq, ht, zero_smul]
  · rcases smul_eq_zero.1 hm with h | h
    · exact absurd (pow_eq_zero_iff'.1 h).1 ht
    · rw [h, zero_mul]

theorem mul_self_eq_one_of_pow_two_pow {F : Type} [Field F] [CharP F 2] {g : GL (Fin 2) F}
    {n : ℕ} (h : g ^ (2 ^ n) = 1) : g * g = 1 := by
  set A : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hAdef
  have hA : A ^ (2 ^ n) = 1 := by
    have := congrArg Units.val h
    simpa [hAdef] using this
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 :=
    ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
  have hN : (A + 1) ^ (m + 1) = 0 := by
    rw [← hm, add_one_pow_two_pow, hA]
    exact add_self_eq_zero_matrix (1 : Matrix (Fin 2) (Fin 2) F)
  have hsq := mul_self_eq_zero_of_pow_succ_eq_zero _ hN
  have h1 : A * A + (A + A) + 1 = 0 := by
    have e : (A + 1) * (A + 1) = A * A + (A + A) + 1 := by noncomm_ring
    rw [← e]
    exact hsq
  rw [add_self_eq_zero_matrix, add_zero] at h1
  have hAA : A * A = 1 := by
    calc A * A = A * A + (1 + 1) := by rw [add_self_eq_zero_matrix 1, add_zero]
      _ = (A * A + 1) + 1 := by abel
      _ = 1 := by rw [h1, zero_add]
  exact Units.ext (by simpa [hAdef] using hAA)

theorem isMulCommutative_of_isPGroup_two_GL2 {F : Type} [Field F] [Finite F] [CharP F 2]
    {S : Subgroup (GL (Fin 2) F)} (hS : IsPGroup 2 S) : IsMulCommutative S := by
  have hsq : ∀ x : S, x * x = 1 := by
    intro x
    obtain ⟨n, hn⟩ := hS x
    apply Subtype.ext
    have h1 : (x : GL (Fin 2) F) ^ (2 ^ n) = 1 := by
      have := congrArg (fun y : S => (y : GL (Fin 2) F)) hn
      simpa using this
    simpa using mul_self_eq_one_of_pow_two_pow h1
  refine ⟨⟨fun a b => ?_⟩⟩
  show a * b = b * a
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hsq (a * b))
  rw [mul_inv_rev, ha, hb] at hab
  exact hab.symm

end GL2

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.OvergroupLeaves

end
