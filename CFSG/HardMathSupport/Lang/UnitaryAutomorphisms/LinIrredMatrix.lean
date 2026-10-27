module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.CubicFrame
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix

variable {K : Type} [Field K]

theorem lin_exists_primitiveRoot_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, IsPrimitiveRoot ω 3 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    exact h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  have hprim : IsPrimitiveRoot x 3 := hx ▸ IsPrimitiveRoot.orderOf x
  exact ⟨_, IsPrimitiveRoot.map_of_injective (f := Units.coeHom K) hprim Units.val_injective⟩

theorem lin_irred_core (ω l : K) (hω3 : ω ^ 3 = 1) (Bm Q Qi : Matrix (Fin 3) (Fin 3) K)
    (hQ : Q * Qi = 1) (hQ' : Qi * Q = 1)
    (hBQ : Bm * Q = Q * !![0, 0, l; 1, 0, 0; 0, 1, 0]) :
    (Q * Matrix.diagonal ![1, ω, ω ^ 2] * Qi).det = 1 ∧
      (Q * Matrix.diagonal ![1, ω, ω ^ 2] * Qi) ^ 3 = 1 ∧
      Bm * (Q * Matrix.diagonal ![1, ω, ω ^ 2] * Qi) =
        ω⁻¹ • ((Q * Matrix.diagonal ![1, ω, ω ^ 2] * Qi) * Bm) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hinv : ω⁻¹ = ω ^ 2 := by
    field_simp
    linear_combination -hω3
  set C : Matrix (Fin 3) (Fin 3) K := !![0, 0, l; 1, 0, 0; 0, 1, 0] with hC
  set D : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, ω, ω ^ 2] with hD
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) K,
      (Q * X * Qi) * (Q * Y * Qi) = Q * (X * Y) * Qi := by
    intro X Y
    calc (Q * X * Qi) * (Q * Y * Qi) = Q * X * (Qi * Q) * Y * Qi := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ']; simp [Matrix.mul_assoc]
  have hD3 : D * D * D = 1 := by
    simp only [hD, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp <;> first | linear_combination hω3 | linear_combination (ω ^ 3 + 1) * hω3
  have hCD : C * D = ω⁻¹ • (D * C) := by
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hC, hD, Matrix.mul_apply, Matrix.diagonal_apply] <;>
      first | ring1 | linear_combination (-1) * hω3 | linear_combination (-ω) * hω3
  have hQiB : Qi * Bm = C * Qi := by
    calc Qi * Bm = Qi * Bm * (Q * Qi) := by rw [hQ, Matrix.mul_one]
      _ = Qi * (Bm * Q) * Qi := by simp only [Matrix.mul_assoc]
      _ = C * Qi := by rw [hBQ]; simp only [← Matrix.mul_assoc, hQ', Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hD, Matrix.det_diagonal]
    have h1 : Q.det * Qi.det = 1 := by rw [← Matrix.det_mul, hQ, Matrix.det_one]
    simp only [Fin.prod_univ_three]
    simp
    calc Q.det * (ω * ω ^ 2) * Qi.det = (Q.det * Qi.det) * ω ^ 3 := by ring
      _ = 1 := by rw [h1, hω3, one_mul]
  · have hQ1 : Q * (1 : Matrix (Fin 3) (Fin 3) K) * Qi = 1 := by
      rw [Matrix.mul_one, hQ]
    rw [pow_succ, pow_succ, pow_one, hmul, hmul, hD3, hQ1]
  · calc Bm * (Q * D * Qi) = Q * (C * D) * Qi := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBQ]; simp only [Matrix.mul_assoc]
      _ = ω⁻¹ • (Q * D * (C * Qi)) := by
          rw [hCD]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = ω⁻¹ • ((Q * D * Qi) * Bm) := by
          rw [← hQiB]
          simp only [Matrix.mul_assoc]

theorem exists_lin_irred_element [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (B : GL (Fin 3) K) {l : K}
    (hB3 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = l • (1 : Matrix (Fin 3) (Fin 3) K))
    (hl : ∀ x : K, x ^ 3 ≠ l) :
    ∃ (ω : K) (H : Matrix.SpecialLinearGroup (Fin 3) K),
      ω ^ 3 = 1 ∧ ω ≠ 1 ∧ H ^ 3 = 1 ∧
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (H : Matrix (Fin 3) (Fin 3) K) =
        ω⁻¹ • ((H : Matrix (Fin 3) (Fin 3) K) * ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  classical
  obtain ⟨ω, hω⟩ := lin_exists_primitiveRoot_three (K := K) h3
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := by
    intro h1
    have := hω.eq_orderOf
    rw [h1, orderOf_one] at this
    omega
  set Bm : Matrix (Fin 3) (Fin 3) K := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hBm
  set w : Fin 3 → K := Pi.single 0 1 with hw
  have hw0 : w ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hw] at this
  set Q : Matrix (Fin 3) (Fin 3) K := (Matrix.of ![w, Bm *ᵥ w, (Bm ^ 2) *ᵥ w])ᵀ with hQ
  have hu : IsUnit Q := by
    have hli := cyc_linearIndependent Bm hB3 hl hw0
    have hcol : Q.col = ![w, Bm *ᵥ w, (Bm ^ 2) *ᵥ w] := by
      ext j i
      fin_cases j <;> simp [hQ]
    exact Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
  have hdu : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hu
  have hQ1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdu
  have hQ2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdu
  have hBQ : Bm * Q = Q * !![0, 0, l; 1, 0, 0; 0, 1, 0] := by
    have hc1 : Bm *ᵥ (Bm *ᵥ w) = (Bm ^ 2) *ᵥ w := by
      rw [Matrix.mulVec_mulVec, pow_two]
    have hc2 : Bm *ᵥ ((Bm ^ 2) *ᵥ w) = l • w := by
      rw [Matrix.mulVec_mulVec, ← pow_succ', pow_three_mulVec hB3]
    ext i k
    fin_cases k
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hQ]
    · have := congrFun hc1 i
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hQ] at this ⊢
      exact this
    · have := congrFun hc2 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hQ] at this ⊢
      linear_combination this
  obtain ⟨hdet, hH3, hBH⟩ := lin_irred_core ω l hω3 Bm Q Q⁻¹ hQ1 hQ2 hBQ
  set Hs : Matrix.SpecialLinearGroup (Fin 3) K :=
    ⟨Q * Matrix.diagonal ![1, ω, ω ^ 2] * Q⁻¹, hdet⟩ with hHs
  have hcoe : ((Hs ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((1 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hH3
  exact ⟨ω, Hs, hω3, hω1, Subtype.ext hcoe, hBH⟩

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
