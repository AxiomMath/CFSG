module

public import CFSG.GH74.GLS.IVK.Lifted.Companion
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

open Matrix CFSG.GH74.GLS.IVK.Lifted
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

namespace SL2Four

variable {F : Type} [Field F]

theorem gl_det_ne_zero (g : GL (Fin 2) F) : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin 2) (Fin 2) F)).1 g.isUnit).ne_zero

theorem exists_norm_form_eq_one [Finite F] (h2 : (2 : F) ≠ 0) {c : F} (hc : c ≠ 0) :
    ∃ r p : F, c * r ^ 2 - p ^ 2 = 1 := by
  have := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply h2
    have h' : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).2 (by rw [h])
    exact_mod_cast h'
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  have hf : (Polynomial.C c * Polynomial.X ^ 2 - Polynomial.C 1 : Polynomial F).degree = 2 := by
    compute_degree!
  have hg : (-(Polynomial.X ^ 2) : Polynomial F).degree = 2 := by
    compute_degree!
  obtain ⟨r, p, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨r, p, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_neg] at h
  linear_combination h

theorem commuting_pair_false (h2 : (2 : F) ≠ 0) (gz gt : GL (Fin 2) F)
    (hz : ∃ c : F, (gz : Matrix (Fin 2) (Fin 2) F) * (gz : Matrix (Fin 2) (Fin 2) F) = c • 1)
    (ht : ∃ c : F, (gt : Matrix (Fin 2) (Fin 2) F) * (gt : Matrix (Fin 2) (Fin 2) F) = c • 1)
    (hzns : ∀ c : F, (gz : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (htns : ∀ c : F, (gt : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hdist : ∀ c : F, (gz : Matrix (Fin 2) (Fin 2) F) *
      ((gt⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hcomm : (gz : Matrix (Fin 2) (Fin 2) F) * (gt : Matrix (Fin 2) (Fin 2) F) =
      (gt : Matrix (Fin 2) (Fin 2) F) * (gz : Matrix (Fin 2) (Fin 2) F)) : False := by
  obtain ⟨c₁, hc₁⟩ := hz
  obtain ⟨c₂, hc₂⟩ := ht
  obtain ⟨x, y, hxy⟩ := exists_eq_smul_add_of_commute (gz : Matrix (Fin 2) (Fin 2) F) hzns
    (gt : Matrix (Fin 2) (Fin 2) F) hcomm.symm
  have hinv : (gt : Matrix (Fin 2) (Fin 2) F) *
      ((gt⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := Units.mul_inv gt
  rw [hxy] at hc₂
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul,
    hc₁] at hc₂
  have hkey : (2 * x * y) • (gz : Matrix (Fin 2) (Fin 2) F) =
      (c₂ - x * x - y * y * c₁) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    linear_combination (norm := module) hc₂
  by_cases h : 2 * x * y = 0
  · rcases mul_eq_zero.1 h with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact h2 h''
      · subst h''
        by_cases hy : y = 0
        · subst hy
          apply htns 0
          rw [hxy]
          simp
        · apply hdist y⁻¹
          have hZ : (gz : Matrix (Fin 2) (Fin 2) F) = y⁻¹ • (gt : Matrix (Fin 2) (Fin 2) F) := by
            rw [hxy]
            simp [smul_smul, hy]
          rw [hZ, Matrix.smul_mul, hinv]
    · subst h'
      apply htns x
      rw [hxy]
      simp
  · apply hzns ((2 * x * y)⁻¹ * (c₂ - x * x - y * y * c₁))
    have := congrArg (fun M => (2 * x * y)⁻¹ • M) hkey
    simp only [smul_smul, inv_mul_cancel₀ h, one_smul] at this
    exact this

end SL2Four

open SL2Four

variable {F : Type} [Field F]

theorem exists_anti_fixed [Finite F] (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F)
    (hsq : ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = c • 1)
    (hns : ∀ c : F, (g : Matrix (Fin 2) (Fin 2) F) ≠ c • 1) :
    ∃ w : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) * (w : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -(w : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, hc⟩ := hsq
  have hdg := gl_det_ne_zero g
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := congrArg Matrix.det hc
    rw [Matrix.det_mul, zero_smul] at h
    simp at h
    exact hdg h
  obtain ⟨r, p, hrp⟩ := exists_norm_form_eq_one h2 hc0
  obtain ⟨v0, v1, hD⟩ := companion_exists_vec (g : Matrix (Fin 2) (Fin 2) F) hns
  have hginv : (g : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := Units.mul_inv g
  generalize (g : Matrix (Fin 2) (Fin 2) F) = G at *
  generalize ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Gi at *
  set P : Matrix (Fin 2) (Fin 2) F :=
    !![v0, G 0 0 * v0 + G 0 1 * v1; v1, G 1 0 * v0 + G 1 1 * v1] with hP
  set C : Matrix (Fin 2) (Fin 2) F := !![0, c; 1, 0] with hC
  set w₀ : Matrix (Fin 2) (Fin 2) F := !![p, -(c * r); r, -p] with hw₀
  have hPdet : P.det ≠ 0 := by
    rw [hP, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    intro h
    apply hD
    linear_combination h
  have hPdetu : IsUnit P.det := isUnit_iff_ne_zero.2 hPdet
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hPdetu
  have hGP : G * P = P * C := by
    have e00 := congrFun (congrFun hc 0) 0
    have e01 := congrFun (congrFun hc 0) 1
    have e10 := congrFun (congrFun hc 1) 0
    have e11 := congrFun (congrFun hc 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, hC, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination v0 * e00 + v1 * e01
    · linear_combination v0 * e10 + v1 * e11
  have hCw : C * w₀ = -(w₀ * C) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hC, hw₀, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hw₀det : w₀.det = 1 := by
    rw [hw₀, Matrix.det_fin_two]
    simp
    linear_combination hrp
  refine ⟨⟨P * w₀ * P⁻¹, ?_⟩, ?_⟩
  · rw [Matrix.det_conj hPu, hw₀det]
  · have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdetu
    have e2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdetu
    have h1 : P⁻¹ * G = C * P⁻¹ := by
      calc P⁻¹ * G = P⁻¹ * G * (P * P⁻¹) := by rw [e1, Matrix.mul_one]
        _ = P⁻¹ * (G * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P⁻¹ * (P * C) * P⁻¹ := by rw [hGP]
        _ = (P⁻¹ * P) * C * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = C * P⁻¹ := by rw [e2, Matrix.one_mul]
    have hGW : G * (P * w₀ * P⁻¹) = -((P * w₀ * P⁻¹) * G) := by
      calc G * (P * w₀ * P⁻¹) = (G * P) * w₀ * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P * (C * w₀) * P⁻¹ := by rw [hGP]; simp only [Matrix.mul_assoc]
        _ = -(P * (w₀ * C) * P⁻¹) := by rw [hCw]; simp only [Matrix.mul_neg, Matrix.neg_mul]
        _ = -((P * w₀ * P⁻¹) * G) := by
          congr 1
          calc P * (w₀ * C) * P⁻¹ = P * w₀ * (C * P⁻¹) := by simp only [Matrix.mul_assoc]
            _ = P * w₀ * (P⁻¹ * G) := by rw [h1]
            _ = (P * w₀ * P⁻¹) * G := by simp only [Matrix.mul_assoc]
    show G * (P * w₀ * P⁻¹) * Gi = -(P * w₀ * P⁻¹)
    calc G * (P * w₀ * P⁻¹) * Gi = -((P * w₀ * P⁻¹) * G) * Gi := by rw [hGW]
      _ = -((P * w₀ * P⁻¹) * (G * Gi)) := by rw [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(P * w₀ * P⁻¹) := by rw [hginv, Matrix.mul_one]

theorem odd_centralizer_four_group (h2 : (2 : F) ≠ 0) (gz gt : GL (Fin 2) F) (y : SL(2, F))
    (hz : ∃ c : F, (gz : Matrix (Fin 2) (Fin 2) F) * (gz : Matrix (Fin 2) (Fin 2) F) = c • 1)
    (ht : ∃ c : F, (gt : Matrix (Fin 2) (Fin 2) F) * (gt : Matrix (Fin 2) (Fin 2) F) = c • 1)
    (hzns : ∀ c : F, (gz : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (htns : ∀ c : F, (gt : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hdist : ∀ c : F, (gz : Matrix (Fin 2) (Fin 2) F) *
      ((gt⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hcomm : ∃ c : F, (gz : Matrix (Fin 2) (Fin 2) F) * (gt : Matrix (Fin 2) (Fin 2) F) =
      c • ((gt : Matrix (Fin 2) (Fin 2) F) * (gz : Matrix (Fin 2) (Fin 2) F)))
    (hyz : (gz : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) F) * (gz : Matrix (Fin 2) (Fin 2) F))
    (hyt : (gt : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) F) * (gt : Matrix (Fin 2) (Fin 2) F))
    {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) : y = 1 := by
  obtain ⟨c, hc⟩ := hcomm
  have hdZ := gl_det_ne_zero gz
  have hdT := gl_det_ne_zero gt
  have hc2 : (c - 1) * (c + 1) = 0 := by
    have h := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul] at h
    simp only [Fintype.card_fin] at h
    have h3 : (c * c - 1) * ((gz : Matrix (Fin 2) (Fin 2) F).det *
        (gt : Matrix (Fin 2) (Fin 2) F).det) = 0 := by
      linear_combination -h
    rcases mul_eq_zero.1 h3 with h4 | h4
    · linear_combination h4
    · exact absurd h4 (mul_ne_zero hdZ hdT)
  rcases mul_eq_zero.1 hc2 with h1 | h1
  ·
    exfalso
    have hc1 : c = 1 := by linear_combination h1
    subst hc1
    rw [one_smul] at hc
    exact commuting_pair_false h2 gz gt hz ht hzns htns hdist hc
  ·
    have hc1 : c = -1 := by linear_combination h1
    subst hc1
    obtain ⟨x, y', hxy⟩ := exists_eq_smul_add_of_commute (gz : Matrix (Fin 2) (Fin 2) F) hzns
      (y : Matrix (Fin 2) (Fin 2) F) hyz.symm
    rw [hxy] at hyt
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one] at hyt
    rw [hc] at hyt
    have hkey : (2 * y') • ((gt : Matrix (Fin 2) (Fin 2) F) * (gz : Matrix (Fin 2) (Fin 2) F)) =
        0 := by
      linear_combination (norm := module) hyt
    have hTZ : IsUnit ((gt : Matrix (Fin 2) (Fin 2) F) * (gz : Matrix (Fin 2) (Fin 2) F)) :=
      IsUnit.mul gt.isUnit gz.isUnit
    have hy0 : y' = 0 := by
      rcases smul_eq_zero.1 hkey with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h h2
        · exact h
      · exact absurd h hTZ.ne_zero
    subst hy0
    rw [zero_smul, add_zero] at hxy
    have hdet : x * x = 1 := by
      have := y.det_coe
      rw [hxy, Matrix.det_smul, Matrix.det_one] at this
      simpa [sq] using this
    have hpow : x ^ m = 1 := by
      have h := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hym
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hxy,
        smul_pow, one_pow] at h
      have h00 := congrFun (congrFun h 0) 0
      simpa using h00
    have hx : x = 1 := by
      have hx2 : (x - 1) * (x + 1) = 0 := by linear_combination hdet
      rcases mul_eq_zero.1 hx2 with h | h
      · linear_combination h
      · exfalso
        have hxm : x = -1 := by linear_combination h
        rw [hxm, Odd.neg_one_pow hm] at hpow
        apply h2
        linear_combination -hpow
    subst hx
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hxy]
    simp

end CFSG.GH74.GLS.LU.Local
