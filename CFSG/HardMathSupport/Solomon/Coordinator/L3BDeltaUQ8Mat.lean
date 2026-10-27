module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUQ8HeisAux

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix Polynomial CFSG.HardMathSupport.Timmesfeld.CrossChar.HeisAux

variable {K : Type} [Field K]

theorem scalar_of_sq_scalar [CharP K 2] {c : Kˣ} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {A B : GL (Fin 3) K} (hAB : A * B = B * A * Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    {R : Matrix (Fin 3) (Fin 3) K}
    (hRB : (B : Matrix (Fin 3) (Fin 3) K) * R = R * B) {d : K}
    (hR2 : R ^ 2 = d • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ x : K, R = x • (1 : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨x, y, z, hR⟩ := commutant_poly hc3 hc1 hAB (N := R) hRB
  set u : Matrix (Fin 3) (Fin 3) K := (B : Matrix (Fin 3) (Fin 3) K) with hu
  have hA3 : A * B ^ 3 = B ^ 3 * A := by
    have h1 := W_pow (WAB hAB) 3
    unfold W at h1
    rw [hc3, map_one, mul_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  obtain ⟨e, he⟩ := commutant_scalar hc3 hc1 hAB (N := u ^ 3)
    (by have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hA3
        simpa [Units.val_pow_eq_pow_val, hu] using this)
    (by rw [← pow_succ, ← pow_succ'])
  have he0 : e ≠ 0 := by
    intro h0
    have h1 : ((B ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 0 := by
      rw [Units.val_pow_eq_pow_val, ← hu, he, h0, zero_smul]
    exact (Units.ne_zero (B ^ 3)) h1
  have ev : ∀ (a : K) (k : ℕ), aeval u (C a * X ^ k) = a • u ^ k := by
    intro a k
    rw [map_mul, aeval_C, aeval_X_pow, ← Algebra.smul_def]
  set q : K[X] := C x * X ^ 0 + C y * X ^ 1 + C z * X ^ 2 with hq
  have hpoly : R = aeval u q := by
    rw [hq, map_add, map_add, ev, ev, ev, hR, pow_zero, pow_one]
  have hsq : q ^ 2 = C (x ^ 2) * X ^ 0 + C (y ^ 2) * X ^ 2 + C (z ^ 2) * X ^ 4 := by
    rw [hq, CharTwo.add_sq, CharTwo.add_sq]
    simp only [map_pow]
    ring
  have h4 : u ^ 4 = e • u := by
    calc u ^ 4 = u ^ 3 * u := by rw [pow_succ]
      _ = e • u := by rw [he, smul_mul_assoc, one_mul]
  have hR2e : R ^ 2 = x ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K) + (e * z ^ 2) • u +
      y ^ 2 • u ^ 2 := by
    rw [hpoly, ← map_pow, hsq, map_add, map_add, ev, ev, ev, h4, pow_zero, smul_smul,
      mul_comm (z ^ 2) e]
    abel
  have hli := linIndep_Yh hc3 hc1 hAB
  have hli' : LinearIndependent K (fun j : Fin 3 =>
      ((Yh A B ((0 : Fin 3), j) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    hli.comp (fun j : Fin 3 => ((0 : Fin 3), j)) (fun i j h => (Prod.mk.inj h).2)
  rw [Fintype.linearIndependent_iff] at hli'
  have hY : ∀ j : Fin 3, ((Yh A B ((0 : Fin 3), j) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      u ^ (j : ℕ) := by
    intro j
    simp [Yh, hu]
  have hsum : ∑ j : Fin 3, (![x ^ 2 - d, e * z ^ 2, y ^ 2] : Fin 3 → K) j •
      ((Yh A B ((0 : Fin 3), j) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 0 := by
    simp only [Fin.sum_univ_three, hY]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    have h2 := hR2e.symm.trans hR2
    calc (x ^ 2 - d) • (1 : Matrix (Fin 3) (Fin 3) K) + (e * z ^ 2) • u + y ^ 2 • u ^ 2
        = (x ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K) + (e * z ^ 2) • u + y ^ 2 • u ^ 2) -
            d • (1 : Matrix (Fin 3) (Fin 3) K) := by module
      _ = 0 := by rw [← h2, sub_self]
  have hzero := hli' _ hsum
  have hy : y ^ 2 = 0 := by simpa using hzero 2
  have hz2 : e * z ^ 2 = 0 := by simpa using hzero 1
  have hy0 : y = 0 := pow_eq_zero_iff (by norm_num) |>.1 hy
  have hz0 : z = 0 := by
    have := (mul_eq_zero.mp hz2).resolve_left he0
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  exact ⟨x, by rw [hR, hy0, hz0]; simp⟩

end CFSG.HardMathSupport.Solomon.Coordinator
