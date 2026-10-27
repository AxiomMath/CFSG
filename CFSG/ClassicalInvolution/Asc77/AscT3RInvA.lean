module

public import CFSG.ClassicalInvolution.Asc77.AscT3RFix

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3R

open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups

section Norm

variable {F : Type} [Field F]

theorem sigma_sigma {σ : F ≃+* F} (hσ2 : σ * σ = 1) (x : F) : σ (σ x) = x := by
  have := congrArg (fun τ : F ≃+* F => τ x) hσ2
  simpa using this

variable [Finite F]

theorem exists_norm_neg_one (hF : Odd (Nat.card F)) {σ : F ≃+* F} (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) : ∃ μ : F, μ * σ μ = -1 ∧ σ μ ≠ μ := by
  classical
  have hσσ := sigma_sigma hσ2
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF
  obtain ⟨x, hx⟩ : ∃ x : F, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  set θ : F := x - σ x with hθ
  have hσθ : σ θ = -θ := by
    rw [hθ, map_sub, hσσ]
    ring
  have hθ0 : θ ≠ 0 := by
    intro h
    apply hx
    have : x = σ x := sub_eq_zero.mp h
    exact this.symm
  set d : F := θ * θ with hd
  have hσd : σ d = d := by rw [hd, map_mul, hσθ]; ring
  have hodd : Odd (Nat.card (fixField σ)) := odd_natCard_fixField hF hσ2 hσ1
  have : Fintype (fixField σ) := Fintype.ofFinite _
  have hcard : Fintype.card (fixField σ) % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  let dF : fixField σ := ⟨d, mem_fixField.mpr hσd⟩
  have hdF0 : dF ≠ 0 := by
    intro h
    have h' := congrArg Subtype.val h
    simp only [dF, hd, ZeroMemClass.coe_zero] at h'
    exact hθ0 (mul_self_eq_zero.mp h')
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial (fixField σ)))
    (g := (-(Polynomial.C dF) * Polynomial.X ^ 2 : Polynomial (fixField σ)))
    (by
      rw [Polynomial.degree_add_eq_left_of_degree_lt] <;> simp)
    (by
      rw [Polynomial.degree_mul, Polynomial.degree_neg, Polynomial.degree_C hdF0,
        Polynomial.degree_X_pow]
      simp)
    hcard
  have hab' : (a : F) ^ 2 + 1 - d * (b : F) ^ 2 = 0 := by
    have h' := congrArg Subtype.val hab
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_neg, AddMemClass.coe_add, SubmonoidClass.coe_pow,
      OneMemClass.coe_one, NegMemClass.coe_neg, MulMemClass.coe_mul, ZeroMemClass.coe_zero,
      dF] at h'
    linear_combination h'
  have haσ : σ (a : F) = a := mem_fixField.mp a.2
  have hbσ : σ (b : F) = b := mem_fixField.mp b.2
  set μ₀ : F := (a : F) + (b : F) * θ with hμ₀
  have hN₀ : μ₀ * σ μ₀ = -1 := by
    rw [hμ₀, map_add, map_mul, haσ, hbσ, hσθ]
    linear_combination hab' + (-(b : F) ^ 2) * hd
  have hμ₀0 : μ₀ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN₀
    exact one_ne_zero (neg_eq_zero.mp hN₀.symm)
  by_cases hμ : σ μ₀ = μ₀
  ·
    have h1p : 1 + θ ≠ 0 := by
      intro h
      have hθ' : θ = -1 := by linear_combination h
      have : σ θ = θ := by rw [hθ', map_neg, map_one]
      rw [hσθ] at this
      apply h2
      linear_combination this + 2 * hθ'
    have h1m : 1 - θ ≠ 0 := by
      intro h
      have hθ' : θ = 1 := by linear_combination -h
      have : σ θ = θ := by rw [hθ', map_one]
      rw [hσθ, hθ'] at this
      apply h2
      linear_combination -this
    set ν : F := (1 + θ) * (1 - θ)⁻¹ with hν
    have hσν : σ ν = (1 - θ) * (1 + θ)⁻¹ := by
      rw [hν, map_mul, map_add, map_one, hσθ, map_inv₀, map_sub, map_one, hσθ]
      ring
    have hνσν : ν * σ ν = 1 := by
      rw [hσν, hν]
      field_simp
    refine ⟨μ₀ * ν, ?_, ?_⟩
    · rw [map_mul]
      calc μ₀ * ν * (σ μ₀ * σ ν) = (μ₀ * σ μ₀) * (ν * σ ν) := by ring
        _ = -1 := by rw [hN₀, hνσν]; ring
    · intro h
      rw [map_mul, hμ] at h
      have h3 : σ ν = ν := mul_left_cancel₀ hμ₀0 h
      rw [hσν, hν] at h3
      have e1 : (1 - θ) * (1 + θ)⁻¹ * ((1 + θ) * (1 - θ)) = (1 - θ) * (1 - θ) := by
        field_simp
      have e2 : (1 + θ) * (1 - θ)⁻¹ * ((1 + θ) * (1 - θ)) = (1 + θ) * (1 + θ) := by
        field_simp
      have h3' : (1 - θ) * (1 - θ) = (1 + θ) * (1 + θ) := by
        calc (1 - θ) * (1 - θ) = (1 - θ) * (1 + θ)⁻¹ * ((1 + θ) * (1 - θ)) := e1.symm
          _ = (1 + θ) * (1 - θ)⁻¹ * ((1 + θ) * (1 - θ)) := by rw [h3]
          _ = (1 + θ) * (1 + θ) := e2
      apply hθ0
      have h4 : (4 : F) * θ = 0 := by linear_combination -h3'
      have h4' : (4 : F) ≠ 0 := by
        have : (4 : F) = 2 * 2 := by norm_num
        rw [this]
        exact mul_ne_zero h2 h2
      exact (mul_eq_zero.mp h4).resolve_left h4'
  · exact ⟨μ₀, hN₀, hμ⟩

end Norm

section Mat

variable {F : Type} [Field F]

@[expose] def matConjAut (h h' : Matrix (Fin 2) (Fin 2) F) (h1 : h * h' = 1) (h2 : h' * h = 1) :
    MulAut SL(2, F) where
  toFun x := ⟨h * (x : Matrix (Fin 2) (Fin 2) F) * h', by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      ← Matrix.det_mul, h1, Matrix.det_one]⟩
  invFun x := ⟨h' * (x : Matrix (Fin 2) (Fin 2) F) * h, by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      ← Matrix.det_mul, h2, Matrix.det_one]⟩
  left_inv x := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (h' * (h * (x : Matrix (Fin 2) (Fin 2) F) * h') * h) i j = x i j
    rw [show h' * (h * (x : Matrix (Fin 2) (Fin 2) F) * h') * h =
      (h' * h) * (x : Matrix (Fin 2) (Fin 2) F) * (h' * h) by
        simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
  right_inv x := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (h * (h' * (x : Matrix (Fin 2) (Fin 2) F) * h) * h') i j = x i j
    rw [show h * (h' * (x : Matrix (Fin 2) (Fin 2) F) * h) * h' =
      (h * h') * (x : Matrix (Fin 2) (Fin 2) F) * (h * h') by
        simp only [Matrix.mul_assoc], h1, Matrix.one_mul, Matrix.mul_one]
  map_mul' x y := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (h * ((x : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F)) * h') i j =
      (h * (x : Matrix (Fin 2) (Fin 2) F) * h' * (h * (y : Matrix (Fin 2) (Fin 2) F) * h')) i j
    rw [show h * (x : Matrix (Fin 2) (Fin 2) F) * h' * (h * (y : Matrix (Fin 2) (Fin 2) F) * h') =
      h * (x : Matrix (Fin 2) (Fin 2) F) * (h' * h) * (y : Matrix (Fin 2) (Fin 2) F) * h' by
        simp only [Matrix.mul_assoc], h2, Matrix.mul_one]
    simp only [Matrix.mul_assoc]

theorem matConjAut_coe (h h' : Matrix (Fin 2) (Fin 2) F) (h1 : h * h' = 1) (h2 : h' * h = 1)
    (x : SL(2, F)) :
    ((matConjAut h h' h1 h2 x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = h * x * h' := rfl

theorem matConjAut_symm_coe (h h' : Matrix (Fin 2) (Fin 2) F) (h1 : h * h' = 1)
    (h2 : h' * h = 1) (x : SL(2, F)) :
    (((matConjAut h h' h1 h2)⁻¹ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = h' * x * h := rfl

end Mat

section Main

variable {F : Type} [Field F] [Finite F]

theorem exists_conj_eq_conj_mul (hF : Odd (Nat.card F)) {σ : F ≃+* F} (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) {s : SL(2, F)} (hs : slFieldAut F σ s = s) (hss : s * s = -1) :
    ∃ γ : MulAut SL(2, F), γ * slFieldAut F σ * γ⁻¹ = MulAut.conj s * slFieldAut F σ := by
  classical
  obtain ⟨μ, hN, hμσ⟩ := exists_norm_neg_one hF hσ2 hσ1
  set ν : F := σ μ with hν
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN
    exact one_ne_zero (neg_eq_zero.mp hN.symm)
  have hμ2 : 1 + μ * μ ≠ 0 := by
    intro h
    apply hμσ
    have : μ * μ = μ * ν := by linear_combination h - hN
    exact (mul_left_cancel₀ hμ0 this).symm
  set sM : Matrix (Fin 2) (Fin 2) F := (s : Matrix (Fin 2) (Fin 2) F) with hsM
  have hssM : sM * sM = -1 := by
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hss
    simpa using this
  have hsσ : sM.map σ = sM := by
    ext i j
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) i j) hs
    simpa [slFieldAut_apply] using this
  have hkey : (1 + μ • sM) * (1 - μ • sM) = (1 + μ * μ) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have e : (μ • sM) * (μ • sM) = (μ * μ) • (sM * sM) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    calc (1 + μ • sM) * (1 - μ • sM) = 1 - (μ • sM) * (μ • sM) := by
          simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
          abel
      _ = 1 - (μ * μ) • (sM * sM) := by rw [e]
      _ = (1 + μ * μ) • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [hssM, smul_neg, sub_neg_eq_add, add_smul, one_smul]
  set h : Matrix (Fin 2) (Fin 2) F := 1 + μ • sM with hh
  set h' : Matrix (Fin 2) (Fin 2) F := (1 + μ * μ)⁻¹ • (1 - μ • sM) with hh'
  have hh1 : h * h' = 1 := by
    rw [hh', Matrix.mul_smul, hh, hkey, smul_smul, inv_mul_cancel₀ hμ2, one_smul]
  have hh2 : h' * h = 1 := mul_eq_one_comm.mp hh1
  set k : Matrix (Fin 2) (Fin 2) F := h.map σ with hk
  set k' : Matrix (Fin 2) (Fin 2) F := h'.map σ with hk'
  have hkk1 : k * k' = 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M.map σ) hh1
    simpa [hk, hk', Matrix.map_mul] using this
  have hkk2 : k' * k = 1 := mul_eq_one_comm.mp hkk1
  have hkexp : k = 1 + ν • sM := by
    rw [hk, hh]
    ext i j
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, hν]
    left
    exact congrFun (congrFun hsσ i) j
  have hA : h = μ • (sM * k) := by
    rw [hkexp, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hssM, smul_add, smul_smul, hN,
      smul_neg, neg_smul, one_smul, neg_neg, hh, add_comm]
  have h1 : μ • (h' * (sM * k)) = 1 := by
    have := hh2
    rw [hA, Matrix.mul_smul] at this
    exact this
  have hB1 : k' = μ • (h' * sM) := by
    calc k' = 1 * k' := (Matrix.one_mul _).symm
      _ = (μ • (h' * (sM * k))) * k' := by rw [h1]
      _ = μ • (h' * sM * (k * k')) := by simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = μ • (h' * sM) := by rw [hkk1, Matrix.mul_one]
  have hB2 : h' = (-μ⁻¹) • (k' * sM) := by
    have e : k' * sM = -(μ • h') := by
      rw [hB1, Matrix.smul_mul, Matrix.mul_assoc, hssM, Matrix.mul_neg, Matrix.mul_one, smul_neg]
    rw [e, neg_smul_neg, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hC : h * k' = μ • sM := by
    rw [hA, Matrix.smul_mul, Matrix.mul_assoc, hkk1, Matrix.mul_one]
  have hD : k * h' = (-μ⁻¹) • sM := by
    conv_lhs => rw [hB2]
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hkk1, Matrix.one_mul]
  have hcoe : ∀ y : SL(2, F), ((slFieldAut F σ y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) F).map σ := fun y => rfl
  have hsinv : s⁻¹ = -s := by
    refine inv_eq_of_mul_eq_one_right ?_
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have : ((s * -s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.mul_neg,
        ← hsM, hssM, neg_neg]
    rw [this]
    rfl
  refine ⟨matConjAut h h' hh1 hh2, ?_⟩
  ext x
  have hL : (((matConjAut h h' hh1 hh2 * slFieldAut F σ * (matConjAut h h' hh1 hh2)⁻¹) x :
      SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      -(sM * (x : Matrix (Fin 2) (Fin 2) F).map σ * sM) := by
    show h * (((slFieldAut F σ) ((matConjAut h h' hh1 hh2)⁻¹ x) : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) * h' = _
    rw [hcoe, matConjAut_symm_coe, Matrix.map_mul, Matrix.map_mul]
    calc h * (h'.map σ * (x : Matrix (Fin 2) (Fin 2) F).map σ * h.map σ) * h'
        = (h * k') * (x : Matrix (Fin 2) (Fin 2) F).map σ * (k * h') := by
          simp only [hk, hk', Matrix.mul_assoc]
      _ = (μ • sM) * (x : Matrix (Fin 2) (Fin 2) F).map σ * ((-μ⁻¹) • sM) := by rw [hC, hD]
      _ = -(sM * (x : Matrix (Fin 2) (Fin 2) F).map σ * sM) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          rw [show -μ⁻¹ * μ = -1 by field_simp, neg_one_smul]
  have hR : (((MulAut.conj s * slFieldAut F σ) x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      -(sM * (x : Matrix (Fin 2) (Fin 2) F).map σ * sM) := by
    show ((s * slFieldAut F σ x * s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = _
    rw [hsinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_neg, hcoe, Matrix.mul_neg, ← hsM]
  rw [hL, hR]

end Main

end CFSG.ClassicalInvolution.Asc77.T3CII.T3R
