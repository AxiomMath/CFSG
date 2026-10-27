module

public import CFSG.GH74.Generic.BProg.B3.L2CompSymD8
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Generic.S45.LUniReal

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompU3Conj

open Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.GH74.Generic.S45.Uni

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

include h in
theorem conj_aux {P R A c : Matrix (Fin n) (Fin n) K} {b : K} (hPu : IsUnit P.det) (hb0 : b ≠ 0)
    (hP : b • (A * P.map h.bar) = P) (hcP : c * P = P * R) (hRbar : R.map h.bar = R)
    (hRG : Rᵀ * ((P.map h.bar)ᵀ * P) * R = (P.map h.bar)ᵀ * P) (hRdet : R.det = 1) :
    (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧ A * c.map h.bar = c * A := by
  refine ⟨?_, ?_, ?_⟩
  · apply mat_cancel_conj hPu (isUnit_det_transpose (isUnit_det_map_bar h hPu))
      (Q := (P.map h.bar)ᵀ)
    have e : (P.map h.bar)ᵀ * ((c.map h.bar)ᵀ * c) * P = ((c * P).map h.bar)ᵀ * (c * P) := by
      rw [Matrix.map_mul, transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [e, hcP, Matrix.map_mul, hRbar, transpose_mul, Matrix.mul_one]
    calc Rᵀ * (P.map h.bar)ᵀ * (P * R) = Rᵀ * ((P.map h.bar)ᵀ * P) * R := by
          simp only [Matrix.mul_assoc]
      _ = (P.map h.bar)ᵀ * P := hRG
  · have h1 : c.det * P.det = P.det * R.det := by
      rw [← det_mul, ← det_mul, hcP]
    have h3 : (c.det - 1) * P.det = 0 := by linear_combination h1 + P.det * hRdet
    have := (mul_eq_zero.1 h3).resolve_right hPu.ne_zero
    linear_combination this
  · apply mat_cancel_right (isUnit_det_map_bar h hPu)
    have hAP : A * P.map h.bar = b⁻¹ • P := by
      have := congrArg (fun M => b⁻¹ • M) hP
      simp only [smul_smul, inv_mul_cancel₀ hb0, one_smul] at this
      exact this
    have hcbar : c.map h.bar * P.map h.bar = P.map h.bar * R := by
      rw [← Matrix.map_mul, hcP, Matrix.map_mul, hRbar]
    calc A * c.map h.bar * P.map h.bar = A * (c.map h.bar * P.map h.bar) := by
          rw [Matrix.mul_assoc]
      _ = A * (P.map h.bar * R) := by rw [hcbar]
      _ = (A * P.map h.bar) * R := by rw [Matrix.mul_assoc]
      _ = b⁻¹ • (P * R) := by rw [hAP, Matrix.smul_mul]
      _ = b⁻¹ • (c * P) := by rw [hcP]
      _ = c * (b⁻¹ • P) := by rw [Matrix.mul_smul]
      _ = c * (A * P.map h.bar) := by rw [hAP]
      _ = c * A * P.map h.bar := by rw [Matrix.mul_assoc]

theorem exists_class2_D8 (h2 : (2 : K) ≠ 0) (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) K} {ε : K}
    (hε : ε = 1 ∨ ε = -1)
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = ε • 1)
    (hR : ∀ (εF : h.fixedField) (G' : Matrix (Fin n) (Fin n) h.fixedField),
      (εF : K) = ε → G'ᵀ = εF • G' → IsUnit G'.det →
        ∃ R₀ S₀ : Matrix (Fin n) (Fin n) h.fixedField, R₀ᵀ * G' * R₀ = G' ∧ R₀.det = 1 ∧
          (∀ l : h.fixedField, R₀ * R₀ ≠ l • 1) ∧ R₀ * R₀ * (R₀ * R₀) = 1 ∧
          S₀ᵀ * G' * S₀ = G' ∧ S₀.det = 1 ∧ S₀ * S₀ = 1 ∧ S₀ * R₀ * S₀ = R₀ * R₀ * R₀) :
    ∃ c d : Matrix (Fin n) (Fin n) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
      (d.map h.bar)ᵀ * d = 1 ∧ d.det = 1 ∧
      (∀ l : K, c * c ≠ l • 1) ∧ c * c * (c * c) = 1 ∧ d * d = 1 ∧ d * c * d = c * c * c ∧
      A * c.map h.bar = c * A ∧ A * d.map h.bar = d * A := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hbε : h.bar ε = ε := by rcases hε with rfl | rfl <;> simp
  obtain ⟨b, hb⟩ := exists_norm_eq h hbε hε0
  obtain ⟨P, hPu, hP⟩ := exists_real_frame h h2 hAA hb hεε
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact hε0 hb.symm
  have hAt := transpose_eq_smul' h hAu hAA hεε
  set G : Matrix (Fin n) (Fin n) K := (P.map h.bar)ᵀ * P with hGdef
  have hGt : Gᵀ = ε • G := gram_transpose h hAt hP
  have hGb : G.map h.bar = Gᵀ := gram_map_bar h P
  obtain ⟨θ₀, hθ0, hθb⟩ : ∃ θ₀ : K, θ₀ ≠ 0 ∧ h.bar θ₀ = ε * θ₀ := by
    rcases hε with rfl | rfl
    · exact ⟨1, one_ne_zero, by simp⟩
    · obtain ⟨θ, hθ0, hθ⟩ := exists_bar_neg h (K := K)
      exact ⟨θ, hθ0, by rw [hθ]; ring⟩
  have hGji : ∀ i j, G j i = ε * G i j := by
    intro i j
    have := congrFun (congrFun hGt i) j
    simpa using this
  have hGentry : ∀ i j, h.bar (θ₀⁻¹ * G i j) = θ₀⁻¹ * G i j := by
    intro i j
    have h1 : h.bar (G i j) = ε * G i j := by
      have := congrFun (congrFun hGb i) j
      simp only [Matrix.map_apply, transpose_apply] at this
      rw [this, hGji]
    rw [map_mul, map_inv₀, hθb, h1]
    field_simp
  let G' : Matrix (Fin n) (Fin n) h.fixedField :=
    Matrix.of fun i j => ⟨θ₀⁻¹ * G i j, hGentry i j⟩
  let sub : h.fixedField →+* K := h.fixedField.subtype
  have hinj : Function.Injective sub := h.fixedField.subtype_injective
  have hG'map : G'.map sub = θ₀⁻¹ • G := by
    ext i j
    rfl
  let εF : h.fixedField := ⟨ε, hbε⟩
  have hεF : (εF : K) = ε := rfl
  have hG'T : G'ᵀ = εF • G' := by
    ext i j
    simp only [transpose_apply, G', of_apply, Matrix.smul_apply, smul_eq_mul, εF]
    rw [hGji i j]
    simp only [Subfield.coe_mul]
    ring
  have hdetG : IsUnit G.det := by
    rw [hGdef, det_mul, det_transpose]
    exact (isUnit_det_map_bar h hPu).mul hPu
  have hdetG' : IsUnit G'.det := by
    have h1 : sub G'.det = (θ₀⁻¹) ^ n * G.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hG'map, det_smul, Fintype.card_fin]
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, map_zero] at h1
    have : (θ₀⁻¹) ^ n * G.det ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (inv_ne_zero hθ0)) hdetG.ne_zero
    exact this h1.symm
  obtain ⟨R₀, S₀, hR1, hR2, hR3, hR4, hS1, hS2, hS3, hS4⟩ := hR εF G' hεF hG'T hdetG'
  have hbarmat : ∀ M : Matrix (Fin n) (Fin n) h.fixedField, (M.map sub).map h.bar = M.map sub := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    exact (M i j).2
  have hGiso : ∀ M : Matrix (Fin n) (Fin n) h.fixedField, Mᵀ * G' * M = G' →
      (M.map sub)ᵀ * G * (M.map sub) = G := by
    intro M hM
    have h1 := congrArg (fun M => M.map sub) hM
    simp only [Matrix.map_mul, Matrix.transpose_map] at h1
    rw [hG'map, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_right_injective _ (inv_ne_zero hθ0) h1
  have hdetmap : ∀ M : Matrix (Fin n) (Fin n) h.fixedField, M.det = 1 → (M.map sub).det = 1 := by
    intro M hM
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hM, map_one]
  obtain ⟨c, hcP⟩ : ∃ c : Matrix (Fin n) (Fin n) K, c * P = P * R₀.map sub := by
    refine ⟨P * R₀.map sub * P⁻¹, ?_⟩
    have : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
    calc P * R₀.map sub * P⁻¹ * P = P * R₀.map sub * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = P * R₀.map sub := by rw [this, Matrix.mul_one]
  obtain ⟨d, hdP⟩ : ∃ d : Matrix (Fin n) (Fin n) K, d * P = P * S₀.map sub := by
    refine ⟨P * S₀.map sub * P⁻¹, ?_⟩
    have : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
    calc P * S₀.map sub * P⁻¹ * P = P * S₀.map sub * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = P * S₀.map sub := by rw [this, Matrix.mul_one]
  obtain ⟨hc1, hc2, hc5⟩ := conj_aux h hPu hb0 hP hcP (hbarmat R₀) (hGiso R₀ hR1) (hdetmap R₀ hR2)
  obtain ⟨hd1, hd2, hd5⟩ := conj_aux h hPu hb0 hP hdP (hbarmat S₀) (hGiso S₀ hS1) (hdetmap S₀ hS2)
  have hcPM : ∀ M : Matrix (Fin n) (Fin n) K, c * (P * M) = P * (R₀.map sub * M) := by
    intro M
    rw [← Matrix.mul_assoc, hcP, Matrix.mul_assoc]
  have hdPM : ∀ M : Matrix (Fin n) (Fin n) K, d * (P * M) = P * (S₀.map sub * M) := by
    intro M
    rw [← Matrix.mul_assoc, hdP, Matrix.mul_assoc]
  refine ⟨c, d, hc1, hc2, hd1, hd2, ?_, ?_, ?_, ?_, hc5, hd5⟩
  · intro l hl
    have hRR : R₀.map sub * R₀.map sub = l • 1 := by
      apply mat_cancel_left hPu
      calc P * (R₀.map sub * R₀.map sub) = c * (P * R₀.map sub) := (hcPM _).symm
        _ = c * (c * P) := by rw [hcP]
        _ = (c * c) * P := by rw [Matrix.mul_assoc]
        _ = P * (l • 1) := by rw [hl, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
              Matrix.mul_one]
    let i₀ : Fin n := ⟨0, hn⟩
    have hmap : (R₀ * R₀).map sub = l • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.map_mul]
      exact hRR
    have hl0 : sub ((R₀ * R₀) i₀ i₀) = l := by
      have := congrFun (congrFun hmap i₀) i₀
      simpa [Matrix.map_apply] using this
    apply hR3 ((R₀ * R₀) i₀ i₀)
    apply Matrix.map_injective hinj
    dsimp only
    rw [hmap]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hl0]
    · simp [hij]
  · apply mat_cancel_right hPu
    rw [Matrix.one_mul]
    have hR4' : R₀.map sub * (R₀.map sub * (R₀.map sub * R₀.map sub)) = 1 := by
      have := congrArg (fun M => M.map sub) hR4
      simp only [Matrix.map_mul] at this
      rw [← Matrix.mul_assoc]
      simpa using this
    calc c * c * (c * c) * P = c * (c * (c * (c * P))) := by simp only [Matrix.mul_assoc]
      _ = P * (R₀.map sub * (R₀.map sub * (R₀.map sub * R₀.map sub))) := by
          rw [hcP, hcPM, hcPM, hcPM]
      _ = P := by rw [hR4', Matrix.mul_one]
  · apply mat_cancel_right hPu
    rw [Matrix.one_mul]
    have hS3' : S₀.map sub * (S₀.map sub * (1 : Matrix (Fin n) (Fin n) K)) = 1 := by
      have := congrArg (fun M => M.map sub) hS3
      simp only [Matrix.map_mul] at this
      rw [Matrix.mul_one, this, Matrix.map_one sub (map_zero sub) (map_one sub)]
    calc d * d * P = d * (d * (P * 1)) := by rw [Matrix.mul_one, Matrix.mul_assoc]
      _ = P * (S₀.map sub * (S₀.map sub * 1)) := by rw [hdPM, hdPM]
      _ = P := by rw [hS3', Matrix.mul_one]
  · apply mat_cancel_right hPu
    have hS4' : S₀.map sub * (R₀.map sub * S₀.map sub) =
        R₀.map sub * (R₀.map sub * R₀.map sub) := by
      have := congrArg (fun M => M.map sub) hS4
      simp only [Matrix.map_mul] at this
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact this
    calc d * c * d * P = d * (c * (d * P)) := by simp only [Matrix.mul_assoc]
      _ = P * (S₀.map sub * (R₀.map sub * S₀.map sub)) := by rw [hdP, hcPM, hdPM]
      _ = P * (R₀.map sub * (R₀.map sub * R₀.map sub)) := by rw [hS4']
      _ = c * (c * (c * P)) := by rw [hcP, hcPM, hcPM]
      _ = c * c * c * P := by simp only [Matrix.mul_assoc]

theorem exists_class2_symm_D8 (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) K}
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = (1 : K) • 1) :
    ∃ c d : Matrix (Fin n) (Fin n) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
      (d.map h.bar)ᵀ * d = 1 ∧ d.det = 1 ∧
      (∀ l : K, c * c ≠ l • 1) ∧ c * c * (c * c) = 1 ∧ d * d = 1 ∧ d * c * d = c * c * c ∧
      A * c.map h.bar = c * A ∧ A * d.map h.bar = d * A := by
  classical
  have : Finite K := h.finite
  have : Fintype h.fixedField := Fintype.ofFinite _
  refine exists_class2_D8 h h2 (by omega) (Or.inl rfl) hAu hAA ?_
  intro εF G' hεF hG'T hunit
  have hεF1 : εF = 1 := Subtype.ext hεF
  rw [hεF1, one_smul] at hG'T
  obtain ⟨c₀, b₀, hdet, hcG, hnsc, hc4, hbdet, hbG, hb2, hbc⟩ :=
    L2CompSymD8.exists_isometry_D8 (two_ne_zero_fixedField h h2) hn G' hG'T hunit
  refine ⟨c₀ᵀ, b₀ᵀ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [transpose_transpose]
    exact hcG
  · rw [det_transpose]
    exact hdet
  · intro l hl
    apply hnsc l
    have := congrArg Matrix.transpose hl
    rwa [← transpose_mul, transpose_transpose, transpose_smul, transpose_one] at this
  · have := congrArg Matrix.transpose hc4
    simp only [transpose_mul, transpose_one] at this
    exact this
  · rw [transpose_transpose]
    exact hbG
  · rw [det_transpose]
    exact hbdet
  · have := congrArg Matrix.transpose hb2
    rwa [transpose_mul, transpose_one] at this
  · have := congrArg Matrix.transpose hbc
    simp only [transpose_mul, Matrix.mul_assoc] at this ⊢
    exact this

end CFSG.GH74.Generic.BProg.B3.L2CompU3Conj
