module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalHeis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.HardMathSupport.Timmesfeld.CrossChar.HeisAux

variable {K : Type} [Field K]

@[expose] def Yh (A B : GL (Fin 3) K) (p : Fin 3 × Fin 3) : GL (Fin 3) K :=
  A ^ (p.1 : ℕ) * B ^ (p.2 : ℕ)

section Heis

variable {c : Kˣ} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {A B : GL (Fin 3) K}
  (hAB : A * B = B * A * Matrix.GeneralLinearGroup.scalar (Fin 3) c)

include hAB in
theorem WA_Yh (p : Fin 3 × Fin 3) : W A (Yh A B p) (c ^ (p.2 : ℕ)) := by
  have := W_mul_right (W_pow (W_self A) (p.1 : ℕ)) (W_pow (WAB hAB) (p.2 : ℕ))
  simpa [Yh] using this

include hAB in
theorem WB_Yh (p : Fin 3 × Fin 3) : W B (Yh A B p) ((c⁻¹) ^ (p.1 : ℕ)) := by
  have := W_mul_right (W_pow (WBA hAB) (p.1 : ℕ)) (W_pow (W_self B) (p.2 : ℕ))
  simpa [Yh] using this

include hc3 hc1 hAB in
theorem trace_Yh_inv_mul {p q : Fin 3 × Fin 3} (hpq : p ≠ q) :
    Matrix.trace ((((Yh A B q)⁻¹ * Yh A B p : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = 0 := by
  by_cases hj : p.2 = q.2
  · have hi : p.1 ≠ q.1 := fun hi => hpq (Prod.ext hi hj)
    refine trace_zero_of_W (g := B) (d := ((c⁻¹) ^ (q.1 : ℕ))⁻¹ * (c⁻¹) ^ (p.1 : ℕ))
      (W_mul_right (W_inv_right (WB_Yh hAB q)) (WB_Yh hAB p)) ?_
    intro h
    rw [inv_mul_eq_one, inv_pow, inv_pow, _root_.inv_inj] at h
    exact hi (Fin.ext (pow_inj3 hc3 hc1 q.1.2 p.1.2 h).symm)
  · refine trace_zero_of_W (g := A) (d := (c ^ (q.2 : ℕ))⁻¹ * c ^ (p.2 : ℕ))
      (W_mul_right (W_inv_right (WA_Yh hAB q)) (WA_Yh hAB p)) ?_
    intro h
    rw [inv_mul_eq_one] at h
    exact hj (Fin.ext (pow_inj3 hc3 hc1 p.2.2 q.2.2 h.symm))

include hc3 hc1 hAB in
theorem linIndep_Yh : LinearIndependent K
    (fun p : Fin 3 × Fin 3 => ((Yh A B p : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h1 := congrArg (fun N : Matrix (Fin 3) (Fin 3) K =>
    Matrix.trace ((((Yh A B q)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N)) hg
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.mul_zero, Matrix.trace_zero] at h1
  rw [Finset.sum_eq_single q] at h1
  · have e : Matrix.trace ((((Yh A B q)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((Yh A B q : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 3 := by
      rw [← Units.val_mul, inv_mul_cancel]; simp
    rw [e, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right (three_ne_zero' hc3 hc1)
  · intro p _ hp
    have := trace_Yh_inv_mul hc3 hc1 hAB hp
    rw [Units.val_mul] at this
    rw [this, smul_zero]
  · simp

include hc3 hc1 hAB in
theorem commutant_poly {N : Matrix (Fin 3) (Fin 3) K}
    (hB : (B : Matrix (Fin 3) (Fin 3) K) * N = N * B) :
    ∃ x y z : K, N = x • (1 : Matrix (Fin 3) (Fin 3) K) + y • (B : Matrix (Fin 3) (Fin 3) K) +
      z • (B : Matrix (Fin 3) (Fin 3) K) ^ 2 := by
  have hli := linIndep_Yh hc3 hc1 hAB
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [Module.finrank_matrix])
  have hb : ∀ p, b p = ((Yh A B p : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro p; simp [b]
  have hN : N = ∑ p, b.repr N p • ((Yh A B p : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    conv_lhs => rw [← b.sum_repr N]
    simp only [hb]
  have hxB := coeff_aux _ hli (fun p => b.repr N p) B (fun p => (c⁻¹) ^ (p.1 : ℕ))
    (fun p => W_matrix (WB_Yh hAB p)) (by rw [← hN]; exact hB)
  have hz : ∀ p : Fin 3 × Fin 3, (p.1 : ℕ) ≠ 0 → b.repr N p = 0 := by
    intro p h1
    have := hxB p
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] at this
    refine (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr ?_)
    intro h
    have h' : c ^ (p.1 : ℕ) = 1 := by
      apply Units.ext
      have := congrArg (fun x => x⁻¹) h
      simpa using this
    exact h1 (pow_inj3 hc3 hc1 p.1.2 (by norm_num) (h'.trans (pow_zero c).symm))
  refine ⟨b.repr N (0, 0), b.repr N (0, 1), b.repr N (0, 2), ?_⟩
  conv_lhs => rw [hN]
  rw [Fintype.sum_prod_type_right]
  have h0 : ∀ j : Fin 3, ∀ i : Fin 3, i ≠ 0 → b.repr N (i, j) = 0 := fun j i hi =>
    hz (i, j) (fun h => hi (Fin.ext h))
  have hs : ∀ j : Fin 3, ∑ i : Fin 3, b.repr N (i, j) •
      ((Yh A B (i, j) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      b.repr N (0, j) • ((Yh A B (0, j) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro j
    rw [Fin.sum_univ_three, h0 j 1 (by decide), h0 j 2 (by decide), zero_smul, zero_smul,
      add_zero, add_zero]
  simp only [hs, Fin.sum_univ_three]
  have hY : ∀ j : Fin 3, ((Yh A B ((0 : Fin 3), j) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) ^ (j : ℕ) := by
    intro j
    simp [Yh, Units.val_pow_eq_pow_val]
  simp [hY]

end Heis

end CFSG.HardMathSupport.Solomon.Coordinator
