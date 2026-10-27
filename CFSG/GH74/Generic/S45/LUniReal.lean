module

public import CFSG.GH74.Generic.S45.LUniVec
public import CFSG.GH74.Generic.S45.LSymFix

public section

namespace CFSG.GH74.Generic.S45.Uni

open Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem exists_matrix_of_span {S : Set (Fin n → K)} (hS : Submodule.span K S = ⊤) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P.det ∧ ∀ j, (fun i => P i j) ∈ S := by
  obtain ⟨b₀, hb₀S, hspan, hli⟩ := exists_linearIndependent K S
  let bas : Module.Basis b₀ K (Fin n → K) :=
    Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  let std := Pi.basisFun K (Fin n)
  let e : b₀ ≃ Fin n := bas.indexEquiv std
  let bas' := bas.reindex e
  refine ⟨std.toMatrix bas', ?_, fun j => ?_⟩
  · rw [← Module.Basis.det_apply]
    exact std.isUnit_det bas'
  · have h1 : (fun i => (std.toMatrix bas') i j) = bas' j := by
      funext i
      simp [Module.Basis.toMatrix_apply, std]
    rw [h1]
    have h2 : bas' j = (e.symm j : Fin n → K) := by
      simp [bas', Module.Basis.reindex_apply, bas, Module.Basis.mk_apply]
    rw [h2]
    exact hb₀S (e.symm j).2

section Real

@[expose] noncomputable def barv (z : Fin n → K) : Fin n → K := fun i => h.bar (z i)

theorem barv_barv (z : Fin n → K) : barv h (barv h z) = z := by
  funext i
  simp [barv, h.bar_bar]

theorem barv_add (z w : Fin n → K) : barv h (z + w) = barv h z + barv h w := by
  funext i
  simp [barv]

theorem barv_smul (c : K) (z : Fin n → K) : barv h (c • z) = h.bar c • barv h z := by
  funext i
  simp [barv]

theorem barv_mulVec (M : Matrix (Fin n) (Fin n) K) (z : Fin n → K) :
    barv h (M *ᵥ z) = M.map h.bar *ᵥ barv h z := by
  funext i
  simp [barv, mulVec, dotProduct, map_sum, map_mul]

@[expose] noncomputable def realJ (A : Matrix (Fin n) (Fin n) K) (b : K) (z : Fin n → K) : Fin n → K :=
  b • (A *ᵥ barv h z)

theorem realJ_add (A : Matrix (Fin n) (Fin n) K) (b : K) (z w : Fin n → K) :
    realJ h A b (z + w) = realJ h A b z + realJ h A b w := by
  simp [realJ, barv_add, mulVec_add]

theorem realJ_sub (A : Matrix (Fin n) (Fin n) K) (b : K) (z w : Fin n → K) :
    realJ h A b (z - w) = realJ h A b z - realJ h A b w := by
  have := realJ_add h A b (z - w) w
  rw [sub_add_cancel] at this
  rw [this]
  abel

theorem realJ_smul (A : Matrix (Fin n) (Fin n) K) (b c : K) (z : Fin n → K) :
    realJ h A b (c • z) = h.bar c • realJ h A b z := by
  simp only [realJ, barv_smul, mulVec_smul, smul_comm b (h.bar c)]

theorem realJ_realJ {A : Matrix (Fin n) (Fin n) K} {ε b : K}
    (hAA : A * A.map h.bar = ε • 1) (hb : h.bar b * b = ε) (hεε : ε * ε = 1) (z : Fin n → K) :
    realJ h A b (realJ h A b z) = z := by
  simp only [realJ, barv_smul, barv_mulVec, barv_barv, mulVec_smul, mulVec_mulVec, hAA,
    smul_mulVec, one_mulVec, smul_smul]
  have : b * (h.bar b * ε) = 1 := by
    calc b * (h.bar b * ε) = (h.bar b * b) * ε := by ring
      _ = 1 := by rw [hb, hεε]
  rw [this, one_smul]

theorem span_real_eq_top (h2 : (2 : K) ≠ 0) {A : Matrix (Fin n) (Fin n) K} {ε b : K}
    (hAA : A * A.map h.bar = ε • 1) (hb : h.bar b * b = ε) (hεε : ε * ε = 1) :
    Submodule.span K {w : Fin n → K | realJ h A b w = w} = ⊤ := by
  obtain ⟨θ, hθ0, hθ⟩ := exists_bar_neg h (K := K)
  rw [eq_top_iff]
  intro z _
  have h1 : realJ h A b (z + realJ h A b z) = z + realJ h A b z := by
    rw [realJ_add, realJ_realJ h hAA hb hεε, add_comm]
  have h2' : realJ h A b (θ • (z - realJ h A b z)) = θ • (z - realJ h A b z) := by
    rw [realJ_smul, hθ, realJ_sub, realJ_realJ h hAA hb hεε, neg_smul, ← smul_neg, neg_sub]
  have hz : z = (2 : K)⁻¹ • ((z + realJ h A b z) + θ⁻¹ • (θ • (z - realJ h A b z))) := by
    rw [smul_smul, inv_mul_cancel₀ hθ0, one_smul]
    have : (z + realJ h A b z) + (z - realJ h A b z) = (2 : K) • z := by module
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hz]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span h1)
    (Submodule.smul_mem _ _ (Submodule.subset_span h2')))

theorem exists_real_frame (h2 : (2 : K) ≠ 0) {A : Matrix (Fin n) (Fin n) K} {ε b : K}
    (hAA : A * A.map h.bar = ε • 1) (hb : h.bar b * b = ε) (hεε : ε * ε = 1) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P.det ∧ b • (A * P.map h.bar) = P := by
  obtain ⟨P, hP, hcol⟩ := exists_matrix_of_span (span_real_eq_top h h2 hAA hb hεε)
  refine ⟨P, hP, ?_⟩
  ext i j
  have := congrFun (hcol j) i
  simp only [realJ, barv, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul]
  exact this

theorem transpose_eq_smul' {A : Matrix (Fin n) (Fin n) K} {ε : K}
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = ε • 1) (hεε : ε * ε = 1) :
    Aᵀ = ε • A := by
  have h1 : Aᵀ * A.map h.bar = 1 := by
    have := congrArg Matrix.transpose hAu
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  have h2 : A.map h.bar * Aᵀ = 1 := mul_eq_one_comm.1 h1
  have h3 : A = ε • Aᵀ := by
    calc A = A * (A.map h.bar * Aᵀ) := by rw [h2, Matrix.mul_one]
      _ = (A * A.map h.bar) * Aᵀ := by rw [Matrix.mul_assoc]
      _ = ε • Aᵀ := by rw [hAA, Matrix.smul_mul, Matrix.one_mul]
  calc Aᵀ = (ε * ε) • Aᵀ := by rw [hεε, one_smul]
    _ = ε • (ε • Aᵀ) := by rw [smul_smul]
    _ = ε • A := by rw [← h3]

theorem map_bar_bar (M : Matrix (Fin n) (Fin n) K) : (M.map h.bar).map h.bar = M := by
  ext i j
  simp [h.bar_bar]

theorem gram_transpose {A P : Matrix (Fin n) (Fin n) K} {ε b : K} (hAt : Aᵀ = ε • A)
    (hP : b • (A * P.map h.bar) = P) :
    ((P.map h.bar)ᵀ * P)ᵀ = ε • ((P.map h.bar)ᵀ * P) := by
  have hG : (P.map h.bar)ᵀ * P = b • ((P.map h.bar)ᵀ * A * P.map h.bar) := by
    calc (P.map h.bar)ᵀ * P = (P.map h.bar)ᵀ * (b • (A * P.map h.bar)) := by rw [hP]
      _ = b • ((P.map h.bar)ᵀ * A * P.map h.bar) := by
        rw [Matrix.mul_smul, Matrix.mul_assoc]
  have hPt : Pᵀ = (b * ε) • ((P.map h.bar)ᵀ * A) := by
    calc Pᵀ = (b • (A * P.map h.bar))ᵀ := by rw [hP]
      _ = b • ((P.map h.bar)ᵀ * Aᵀ) := by rw [transpose_smul, transpose_mul]
      _ = (b * ε) • ((P.map h.bar)ᵀ * A) := by
        rw [hAt, Matrix.mul_smul, smul_smul]
  calc ((P.map h.bar)ᵀ * P)ᵀ = Pᵀ * P.map h.bar := by
        rw [transpose_mul, transpose_transpose]
    _ = ((b * ε) • ((P.map h.bar)ᵀ * A)) * P.map h.bar := by rw [← hPt]
    _ = ε • (b • ((P.map h.bar)ᵀ * A * P.map h.bar)) := by
        rw [Matrix.smul_mul, smul_smul, mul_comm ε b]
    _ = ε • ((P.map h.bar)ᵀ * P) := by rw [hG]

theorem gram_map_bar (P : Matrix (Fin n) (Fin n) K) :
    ((P.map h.bar)ᵀ * P).map h.bar = ((P.map h.bar)ᵀ * P)ᵀ := by
  rw [Matrix.map_mul, transpose_mul, transpose_transpose, ← Matrix.transpose_map,
    map_bar_bar]

theorem mat_cancel_conj {P Q X Y : Matrix (Fin n) (Fin n) K} (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hXY : Q * X * P = Q * Y * P) : X = Y := by
  have hP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQ
  calc X = (Q⁻¹ * Q) * X * (P * P⁻¹) := by rw [hP', hQ', Matrix.one_mul, Matrix.mul_one]
    _ = Q⁻¹ * (Q * X * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = Q⁻¹ * (Q * Y * P) * P⁻¹ := by rw [hXY]
    _ = (Q⁻¹ * Q) * Y * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [hP', hQ', Matrix.one_mul, Matrix.mul_one]

theorem mat_cancel_left {P X Y : Matrix (Fin n) (Fin n) K} (hP : IsUnit P.det)
    (hXY : P * X = P * Y) : X = Y := by
  have hP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  calc X = (P⁻¹ * P) * X := by rw [hP', Matrix.one_mul]
    _ = P⁻¹ * (P * X) := by rw [Matrix.mul_assoc]
    _ = P⁻¹ * (P * Y) := by rw [hXY]
    _ = Y := by rw [← Matrix.mul_assoc, hP', Matrix.one_mul]

theorem mat_cancel_right {P X Y : Matrix (Fin n) (Fin n) K} (hP : IsUnit P.det)
    (hXY : X * P = Y * P) : X = Y := by
  have hP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  calc X = X * (P * P⁻¹) := by rw [hP', Matrix.mul_one]
    _ = (X * P) * P⁻¹ := by rw [← Matrix.mul_assoc]
    _ = (Y * P) * P⁻¹ := by rw [hXY]
    _ = Y := by rw [Matrix.mul_assoc, hP', Matrix.mul_one]

theorem isUnit_det_map_bar {P : Matrix (Fin n) (Fin n) K} (hP : IsUnit P.det) :
    IsUnit (P.map h.bar).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hP.map h.bar

theorem isUnit_det_transpose {P : Matrix (Fin n) (Fin n) K} (hP : IsUnit P.det) :
    IsUnit Pᵀ.det := by
  rwa [det_transpose]

theorem exists_class2 (h2 : (2 : K) ≠ 0) (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) K} {ε : K}
    (hε : ε = 1 ∨ ε = -1)
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = ε • 1)
    (hR : ∀ (εF : h.fixedField) (G' : Matrix (Fin n) (Fin n) h.fixedField),
      (εF : K) = ε → G'ᵀ = εF • G' → IsUnit G'.det →
        ∃ R₀ : Matrix (Fin n) (Fin n) h.fixedField, R₀ᵀ * G' * R₀ = G' ∧ R₀.det = 1 ∧
          (∀ l : h.fixedField, R₀ * R₀ ≠ l • 1) ∧ R₀ * R₀ * (R₀ * R₀) = 1) :
    ∃ c : Matrix (Fin n) (Fin n) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
      (∀ l : K, c * c ≠ l • 1) ∧ c * c * (c * c) = 1 ∧ A * c.map h.bar = c * A := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hbε : h.bar ε = ε := by rcases hε with rfl | rfl <;> simp
  obtain ⟨b, hb⟩ := exists_norm_eq h hbε hε0
  obtain ⟨P, hPu, hP⟩ := exists_real_frame h h2 hAA hb hεε
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
  obtain ⟨R₀, hR1, hR2, hR3, hR4⟩ := hR εF G' hεF hG'T hdetG'
  set R : Matrix (Fin n) (Fin n) K := R₀.map sub with hRdef
  have hRbar : R.map h.bar = R := by
    ext i j
    simp only [Matrix.map_apply, hRdef]
    exact (R₀ i j).2
  have hRG : Rᵀ * G * R = G := by
    have h1 := congrArg (fun M => M.map sub) hR1
    simp only [Matrix.map_mul] at h1
    rw [hG'map, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_right_injective _ (inv_ne_zero hθ0) h1
  obtain ⟨c, hcP⟩ : ∃ c : Matrix (Fin n) (Fin n) K, c * P = P * R := by
    refine ⟨P * R * P⁻¹, ?_⟩
    have : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
    calc P * R * P⁻¹ * P = P * R * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = P * R := by rw [this, Matrix.mul_one]
  have hcPM : ∀ M : Matrix (Fin n) (Fin n) K, c * (P * M) = P * (R * M) := by
    intro M
    rw [← Matrix.mul_assoc, hcP, Matrix.mul_assoc]
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
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
    have h2' : R.det = 1 := by
      rw [hRdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hR2, map_one]
    have h3 : (c.det - 1) * P.det = 0 := by linear_combination h1 + P.det * h2'
    have := (mul_eq_zero.1 h3).resolve_right hPu.ne_zero
    linear_combination this
  · intro l hl
    have hRR : R * R = l • 1 := by
      apply mat_cancel_left hPu
      calc P * (R * R) = c * (P * R) := (hcPM R).symm
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
    have hR4' : R * (R * (R * R)) = 1 := by
      have := congrArg (fun M => M.map sub) hR4
      simp only [Matrix.map_mul] at this
      rw [← Matrix.mul_assoc]
      simpa using this
    calc c * c * (c * c) * P = c * (c * (c * (c * P))) := by simp only [Matrix.mul_assoc]
      _ = P * (R * (R * (R * R))) := by rw [hcP, hcPM, hcPM, hcPM]
      _ = P := by rw [hR4', Matrix.mul_one]
  · apply mat_cancel_right (isUnit_det_map_bar h hPu)
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hb
      exact hε0 hb.symm
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

theorem two_ne_zero_fixedField (h2 : (2 : K) ≠ 0) : (2 : h.fixedField) ≠ 0 := by
  intro h0
  apply h2
  have := congrArg (algebraMap h.fixedField K) h0
  rw [map_ofNat, map_zero] at this
  exact this

theorem exists_class2_symm (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {A : Matrix (Fin n) (Fin n) K}
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = (1 : K) • 1) :
    ∃ c : Matrix (Fin n) (Fin n) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
      (∀ l : K, c * c ≠ l • 1) ∧ c * c * (c * c) = 1 ∧ A * c.map h.bar = c * A := by
  classical
  have : Finite K := h.finite
  have : Fintype h.fixedField := Fintype.ofFinite _
  refine exists_class2 h h2 (by omega) (Or.inl rfl) hAu hAA ?_
  intro εF G' hεF hG'T hunit
  have hεF1 : εF = 1 := Subtype.ext hεF
  rw [hεF1, one_smul] at hG'T
  obtain ⟨c₀, hdet, hcG, hnsc, hc4⟩ := exists_isometry_order_four (two_ne_zero_fixedField h h2) hn
    G' hG'T hunit
  refine ⟨c₀ᵀ, ?_, ?_, ?_, ?_⟩
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

end Real
end CFSG.GH74.Generic.S45.Uni
