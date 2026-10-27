module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4F1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

namespace Sp48

open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F (F8)

theorem two_eq_zero : (2 : F8) = 0 := CharTwo.two_eq_zero

theorem pow_eight (x : F8) : x ^ 8 = x := by
  classical
  haveI : Fintype F8 := Fintype.ofFinite F8
  have h := FiniteField.pow_card x
  rwa [Fintype.card_eq_nat_card, CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F.card_F8] at h

theorem exists_ne_zero_one : ∃ x : F8, x ≠ 0 ∧ x ≠ 1 := by
  by_contra! h
  have hsub : (Set.univ : Set F8) ⊆ {0, 1} := fun x _ => by
    by_cases h0 : x = 0
    · exact Or.inl h0
    · exact Or.inr (h x h0)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F.card_F8] at h1
  have h2 := Set.ncard_insert_le (0 : F8) {1}
  rw [Set.ncard_singleton] at h2
  omega

theorem exists_tau : ∃ τ : F8, τ ^ 3 + τ + 1 = 0 := by
  obtain ⟨x, hx0, hx1⟩ := exists_ne_zero_one
  have h8 : x ^ 8 + x = 0 := by rw [pow_eight]; exact CharTwo.add_self_eq_zero x
  have hfac : x * (x + 1) * ((x ^ 3 + x + 1) * (x ^ 3 + x ^ 2 + 1)) = 0 := by
    linear_combination h8 + (x ^ 7 + x ^ 6 + 2 * x ^ 5 + 2 * x ^ 4 + x ^ 3 + x ^ 2) * two_eq_zero
  have hx1' : x + 1 ≠ 0 := by
    intro h
    apply hx1
    linear_combination h - two_eq_zero
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd h (mul_ne_zero hx0 hx1')
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨x, h⟩
  · refine ⟨x⁻¹, ?_⟩
    have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx0
    field_simp
    linear_combination h

variable {τ : F8} (hτ : τ ^ 3 + τ + 1 = 0)

include hτ in
theorem tau_ne_one : τ ≠ 1 := by
  rintro rfl
  have : (3 : F8) = 0 := by linear_combination hτ
  have h1 : (1 : F8) = 0 := by linear_combination this - two_eq_zero
  exact one_ne_zero h1

@[expose] noncomputable def amat (τ : F8) : Matrix (Fin 2) (Fin 2) F8 := !![0, 1; 1, τ]

@[expose] noncomputable def amatInv (τ : F8) : Matrix (Fin 2) (Fin 2) F8 := !![τ, 1; 1, 0]

@[expose] noncomputable def jmat : Matrix (Fin 2) (Fin 2) F8 := !![0, 1; 1, 0]

theorem amat_mul_inv : amat τ * amatInv τ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amat, amatInv, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem amatInv_mul : amatInv τ * amat τ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amat, amatInv, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem jmat_mul_self : jmat * jmat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jmat, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_amat : (amat τ).det = 1 := by
  simp only [amat, Matrix.det_fin_two_of]
  linear_combination -two_eq_zero

theorem det_jmat : jmat.det = 1 := by
  simp only [jmat, Matrix.det_fin_two_of]
  linear_combination -two_eq_zero

theorem jmat_conj_amat : jmat * amat τ * jmat = amatInv τ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jmat, amat, amatInv, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] noncomputable def lin (τ u v : F8) : Matrix (Fin 2) (Fin 2) F8 := u • amat τ + v • 1

theorem lin_mul_amat (u v : F8) : lin τ u v * amat τ = lin τ (u * τ + v) u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lin, amat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem amat_eq_lin : amat τ = lin τ 1 0 := by
  simp [lin]

theorem step {n : ℕ} {u v u' : F8} (h : amat τ ^ n = lin τ u v) (hu : u * τ + v = u') :
    amat τ ^ (n + 1) = lin τ u' u := by
  rw [pow_succ, h, lin_mul_amat, hu]

theorem lin_zero_one : lin τ 0 1 = 1 := by simp [lin]

include hτ in
theorem amat_pow_three : amat τ ^ 3 = lin τ (τ ^ 2 + 1) τ := by
  have p1 : amat τ ^ 1 = lin τ 1 0 := by rw [pow_one, amat_eq_lin]
  have p2 := step p1 (u' := τ) (by ring)
  exact step p2 (by ring)

include hτ in
theorem amat_pow_nine : amat τ ^ 9 = 1 := by
  have h2 := two_eq_zero
  have p4 := step (amat_pow_three hτ) (u' := τ + 1) (by linear_combination hτ - h2)
  have p5 := step p4 (u' := τ + 1) (by linear_combination τ ^ 2 * h2)
  have p6 := step p5 (u' := τ ^ 2 + 1) (by linear_combination τ * h2)
  have p7 := step p6 (u' := τ) (by linear_combination hτ)
  have p8 := step p7 (u' := 1) (by linear_combination τ ^ 2 * h2)
  have p9 := step p8 (u' := 0) (by linear_combination τ * h2)
  rw [p9, lin_zero_one]

include hτ in
theorem amat_pow_three_ne_one : amat τ ^ 3 ≠ 1 := by
  intro h
  rw [amat_pow_three hτ] at h
  have h01 := congrFun (congrFun h 0) 1
  simp [lin, amat, Matrix.one_apply] at h01
  have : (τ + 1) ^ 2 = 0 := by linear_combination h01 + τ * two_eq_zero
  have h1 : τ + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  exact tau_ne_one hτ (by linear_combination h1 - two_eq_zero)

end Sp48

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
