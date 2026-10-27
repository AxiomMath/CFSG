module

public import CFSG.ClassicalInvolution.ModelFacts.L6CUBase
public import CFSG.ClassicalInvolution.ModelFacts.L6CGraph
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen
public import CFSG.ClassicalInvolution.ModelFacts.L6CUInner

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) K

@[expose] noncomputable def barEq : K ≃+* K :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem barEq_apply (c : K) : barEq h c = h.bar c := rfl

theorem exists_descent {M' : 𝕄₄} (hM' : M' * M'.map h.bar = 1) :
    ∃ H : GL (Fin 4) K, M' * (H : 𝕄₄).map h.bar = (H : 𝕄₄) := by
  obtain ⟨x₀, hx₀⟩ := h.exists_bar_ne
  let T : (Fin 4 → K) → (Fin 4 → K) := fun v => M' *ᵥ fun i => h.bar (v i)
  have hbarvec : ∀ (N : 𝕄₄) (v : Fin 4 → K), (fun i => h.bar ((N *ᵥ v) i)) =
      N.map h.bar *ᵥ fun i => h.bar (v i) := fun N v => funext fun i =>
    RingHom.map_mulVec h.bar N v i
  obtain ⟨H, hH⟩ := exists_fixed_basis_of_ne (σ := barEq h) (x₀ := x₀)
    (by rw [barEq_apply]; exact hx₀) T
    (fun v w => by
      show M' *ᵥ (fun i => h.bar (v i + w i)) =
        M' *ᵥ (fun i => h.bar (v i)) + M' *ᵥ (fun i => h.bar (w i))
      rw [← Matrix.mulVec_add]
      congr 1
      funext i
      simp)
    (fun c v => by
      show M' *ᵥ (fun i => h.bar (c * v i)) = barEq h c • (M' *ᵥ fun i => h.bar (v i))
      rw [barEq_apply, ← Matrix.mulVec_smul]
      congr 1
      funext i
      simp)
    (fun v => by
      show M' *ᵥ (fun i => h.bar ((M' *ᵥ fun i => h.bar (v i)) i)) = v
      rw [hbarvec M' (fun i => h.bar (v i))]
      have hv : (fun i => h.bar (h.bar (v i))) = v := funext fun i => h.bar_bar _
      rw [hv, Matrix.mulVec_mulVec, hM', Matrix.one_mulVec])
  refine ⟨H, ?_⟩
  ext r c
  have := congrFun (hH c) r
  simpa [T, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem gram_conj {M H : 𝕄₄} {lam : K} (hM : uadj h M * M = 1)
    (hH : M * H.map h.bar = lam • H) :
    (uadj h H * H).map h.bar = (h.bar lam * lam) • (uadj h H * H) := by
  have h1 : uadj h (M * H.map h.bar) * (M * H.map h.bar) = (uadj h H).map h.bar * H.map h.bar := by
    rw [uadj_mul]
    calc uadj h (H.map h.bar) * uadj h M * (M * H.map h.bar)
        = uadj h (H.map h.bar) * (uadj h M * M) * H.map h.bar := by simp only [Matrix.mul_assoc]
      _ = uadj h (H.map h.bar) * H.map h.bar := by rw [hM, Matrix.mul_one]
      _ = _ := by rw [uadj, uadj, Matrix.transpose_map, map_bar_bar]
  rw [hH, uadj_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h1
  rw [Matrix.map_mul, ← h1]

theorem gram_map_bar (H : 𝕄₄) : (uadj h H * H).map h.bar = (uadj h H * H)ᵀ := by
  rw [Matrix.map_mul, map_bar_uadj, Matrix.transpose_mul, uadj, Matrix.transpose_transpose]

theorem semi_assembly {M H P' Θ Ψ : 𝕄₄} {lam : K}
    (hH : M * H.map h.bar = lam • H) (hP' : P'.map h.bar = P')
    (hQ : uadj h Θ * (uadj h (H * P') * (H * P')) * Θ = 1) (hΘ : Θ * Ψ = Θ.map h.bar)
    (hΨ : (lam • Ψ) * (rot4 K : 𝕄₄) = (rot4 K : 𝕄₄) * (lam • Ψ)) :
    ∃ Q : 𝕄₄, uadj h Q * Q = 1 ∧
      M * ((Q * (rot4 K : 𝕄₄) * uadj h Q).map h.bar) = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by
  set Q : 𝕄₄ := H * P' * Θ with hQdef
  have hQ' : uadj h Q * Q = 1 := by
    rw [hQdef, uadj_mul]
    calc uadj h Θ * uadj h (H * P') * (H * P' * Θ)
        = uadj h Θ * (uadj h (H * P') * (H * P')) * Θ := by simp only [Matrix.mul_assoc]
      _ = 1 := hQ
  refine ⟨Q, hQ', semicomm_of_frame h hQ' (N := lam • Ψ) ?_ hΨ⟩
  have hMQ : M * Q.map h.bar = lam • (Q * Ψ) := by
    rw [hQdef, Matrix.map_mul, Matrix.map_mul, hP', ← hΘ]
    calc M * (H.map h.bar * P' * (Θ * Ψ)) = (M * H.map h.bar) * P' * (Θ * Ψ) := by
          simp only [Matrix.mul_assoc]
      _ = lam • (H * P' * Θ * Ψ) := by
          rw [hH, Matrix.smul_mul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
      _ = lam • (H * P' * Θ * Ψ) := rfl
  calc lam • Ψ = lam • ((uadj h Q * Q) * Ψ) := by rw [hQ', Matrix.one_mul]
    _ = uadj h Q * (lam • (Q * Ψ)) := by
        rw [Matrix.mul_smul, Matrix.mul_assoc]
    _ = uadj h Q * M * Q.map h.bar := by rw [← hMQ, Matrix.mul_assoc]


theorem uadj_diagonal (d : Fin 4 → K) :
    uadj h (Matrix.diagonal d : 𝕄₄) = Matrix.diagonal fun i => h.bar (d i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [uadj]
  · simp [uadj, hij, Ne.symm hij]

theorem exists_norm_eq {d : K} (hd : h.bar d = d) : ∃ t : K, h.bar t * t = d := by
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨d, hd⟩
  exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩

theorem det_uadj (M : 𝕄₄) : (uadj h M).det = h.bar M.det := by
  rw [uadj, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem exists_frame_sym (hp2 : p ≠ 2) {M : 𝕄₄} (hM : uadj h M * M = 1)
    (hMM : M * M.map h.bar = 1) :
    ∃ Q : 𝕄₄, uadj h Q * Q = 1 ∧
      M * ((Q * (rot4 K : 𝕄₄) * uadj h Q).map h.bar) = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by
  have := h.finite
  have h2 : (2 : K) ≠ 0 := UnitaryHigher.two_ne_zero_of_odd h hp2
  obtain ⟨H, hH⟩ := exists_descent h hMM
  set G : 𝕄₄ := uadj h (H : 𝕄₄) * (H : 𝕄₄) with hG
  have hH1 : M * (H : 𝕄₄).map h.bar = (1 : K) • (H : 𝕄₄) := by rw [one_smul]; exact hH
  have hGbar : G.map h.bar = G := by
    have := gram_conj h hM hH1
    rwa [map_one, one_mul, one_smul] at this
  have hGt : Gᵀ = G := by rw [← gram_map_bar, hGbar]
  have hHdet : (H : 𝕄₄).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det H).isUnit
    simpa using this.ne_zero
  have hGdet : G.det ≠ 0 := by
    rw [hG, det_mul, det_uadj]
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hHdet) hHdet
  have hmem : ∀ i j, G i j ∈ h.fixedField := fun i j =>
    h.mem_fixedField.mpr (by simpa [Matrix.map_apply] using congrFun (congrFun hGbar i) j)
  let G₀ : Matrix (Fin 4) (Fin 4) h.fixedField := Matrix.of fun i j => ⟨G i j, hmem i j⟩
  have hG₀ : G₀.map h.fixedField.subtype = G := by
    ext i j
    rfl
  have hG₀t : G₀ᵀ = G₀ := by
    ext i j
    exact congrFun (congrFun hGt i) j
  have hG₀det : G₀.det ≠ 0 := by
    intro h0
    apply hGdet
    rw [← hG₀, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have h2₀ : (2 : h.fixedField) ≠ 0 := fun h0 => h2 (by
    have := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at this
    exact this)
  obtain ⟨P₀, a, c₃, c₄, ha, hc₃, hc₄, hP₀⟩ := exists_congr_diag_aa4 h2₀ hG₀t hG₀det
  have hfix : ∀ x : h.fixedField, h.bar (x : K) = x := fun x => h.mem_fixedField.mp x.2
  set ι := h.fixedField.subtype with hι
  obtain ⟨P', hP'⟩ : ∃ P' : 𝕄₄, P' = (P₀ : Matrix (Fin 4) (Fin 4) h.fixedField).map ι :=
    ⟨_, rfl⟩
  have hP'bar : P'.map h.bar = P' := by
    ext i j
    rw [hP']
    exact hfix _
  have hGram : uadj h ((H : 𝕄₄) * P') * ((H : 𝕄₄) * P') =
      Matrix.diagonal ![(a : K), (a : K), (c₃ : K), (c₄ : K)] := by
    have h1 : uadj h ((H : 𝕄₄) * P') * ((H : 𝕄₄) * P') = P'ᵀ * G * P' := by
      rw [uadj_mul, uadj, hP'bar, hG]
      simp only [uadj, Matrix.mul_assoc]
    rw [h1, ← hG₀, hP']
    have := congrArg (fun X : Matrix (Fin 4) (Fin 4) h.fixedField => X.map ι) hP₀
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [this, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨t₁, ht₁⟩ := exists_norm_eq h (d := ((a : K))⁻¹) (by rw [map_inv₀, hfix a])
  obtain ⟨t₃, ht₃⟩ := exists_norm_eq h (d := ((c₃ : K))⁻¹) (by rw [map_inv₀, hfix c₃])
  obtain ⟨t₄, ht₄⟩ := exists_norm_eq h (d := ((c₄ : K))⁻¹) (by rw [map_inv₀, hfix c₄])
  have ha' : (a : K) ≠ 0 := fun h0 => ha (Subtype.ext h0)
  have hc₃' : (c₃ : K) ≠ 0 := fun h0 => hc₃ (Subtype.ext h0)
  have hc₄' : (c₄ : K) ≠ 0 := fun h0 => hc₄ (Subtype.ext h0)
  let t : Fin 4 → K := ![t₁, t₁, t₃, t₄]
  let g : Fin 4 → K := ![(a : K), (a : K), (c₃ : K), (c₄ : K)]
  have hg : ∀ i, g i ≠ 0 := by
    intro i
    fin_cases i <;> simpa [g]
  have hnormt : ∀ i, h.bar (t i) * t i = (g i)⁻¹ := by
    intro i
    fin_cases i <;> simpa [t, g] using by assumption
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i h0
    have := hnormt i
    rw [h0, map_zero, zero_mul] at this
    exact inv_ne_zero (hg i) this.symm
  have hgd : (Matrix.diagonal ![(a : K), (a : K), (c₃ : K), (c₄ : K)] : 𝕄₄) = Matrix.diagonal g :=
    rfl
  refine semi_assembly h (H := (H : 𝕄₄)) (P' := P') (Θ := Matrix.diagonal t)
    (Ψ := Matrix.diagonal fun i => (t i)⁻¹ * h.bar (t i)) (lam := 1) hH1 hP'bar ?_ ?_ ?_
  · rw [hGram, hgd, uadj_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    calc h.bar (t i) * g i * t i = g i * (h.bar (t i) * t i) := by ring
      _ = 1 := by rw [hnormt i, mul_inv_cancel₀ (hg i)]
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact mul_inv_cancel_left₀ (ht0 i) _
  · rw [one_smul]
    refine diagonal_mul_rot4 ?_
    simp [t]


theorem exists_frame_alt (hp2 : p ≠ 2) (hq4 : p ^ f % 4 = 1) {M : 𝕄₄} (hM : uadj h M * M = 1)
    (hMM : M * M.map h.bar = -1) :
    ∃ Q : 𝕄₄, uadj h Q * Q = 1 ∧
      M * ((Q * (rot4 K : 𝕄₄) * uadj h Q).map h.bar) = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by
  have := h.finite
  have h2 : (2 : K) ≠ 0 := UnitaryHigher.two_ne_zero_of_odd h hp2
  obtain ⟨i, hi, hbi⟩ := exists_sqrt_neg_one h hq4
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hM' : (i • M) * (i • M).map h.bar = 1 := by
    have hmap : (i • M).map h.bar = h.bar i • M.map h.bar := by
      ext a b
      simp [Matrix.map_apply]
    rw [hmap, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMM, hbi, smul_neg, ← neg_smul]
    have : -(i * i) = 1 := by linear_combination -hi
    rw [this, one_smul]
  obtain ⟨H, hH'⟩ := exists_descent h hM'
  have hH1 : M * (H : 𝕄₄).map h.bar = (-i) • (H : 𝕄₄) := by
    have e1 : i • (M * (H : 𝕄₄).map h.bar) = (H : 𝕄₄) := by rw [← Matrix.smul_mul]; exact hH'
    calc M * (H : 𝕄₄).map h.bar = (-i * i) • (M * (H : 𝕄₄).map h.bar) := by
          have : -i * i = 1 := by linear_combination -hi
          rw [this, one_smul]
      _ = (-i) • (i • (M * (H : 𝕄₄).map h.bar)) := by rw [smul_smul]
      _ = (-i) • (H : 𝕄₄) := by rw [e1]
  set G : 𝕄₄ := uadj h (H : 𝕄₄) * (H : 𝕄₄) with hG
  have hnl : h.bar (-i) * (-i) = -1 := by
    rw [map_neg, hbi]
    linear_combination hi
  have hGbar : G.map h.bar = -G := by
    have := gram_conj h hM hH1
    rwa [hnl, neg_one_smul] at this
  have hGt : Gᵀ = -G := by rw [← gram_map_bar, hGbar]
  have hHdet : (H : 𝕄₄).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det H).isUnit
    simpa using this.ne_zero
  have hGdet : G.det ≠ 0 := by
    rw [hG, det_mul, det_uadj]
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hHdet) hHdet
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  set ω : K := c₀ - h.bar c₀ with hω
  have hω0 : ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hc₀)
  have hbω : h.bar ω = -ω := by
    rw [hω, map_sub, h.bar_bar]
    ring
  set Ω : 𝕄₄ := ω⁻¹ • G with hΩ
  have hΩbar : Ω.map h.bar = Ω := by
    have e : Ω.map h.bar = h.bar ω⁻¹ • G.map h.bar := by
      ext a b
      simp [hΩ, Matrix.map_apply]
    rw [e, hGbar, map_inv₀, hbω, inv_neg, smul_neg, neg_smul, neg_neg]
  have hΩt : Ωᵀ = -Ω := by
    rw [hΩ, Matrix.transpose_smul, hGt, smul_neg]
  have hΩdet : Ω.det ≠ 0 := by
    rw [hΩ, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hω0)) hGdet
  have hmem : ∀ a b, Ω a b ∈ h.fixedField := fun a b =>
    h.mem_fixedField.mpr (by simpa [Matrix.map_apply] using congrFun (congrFun hΩbar a) b)
  let Ω₀ : Matrix (Fin 4) (Fin 4) h.fixedField := Matrix.of fun a b => ⟨Ω a b, hmem a b⟩
  have hΩ₀ : Ω₀.map h.fixedField.subtype = Ω := by
    ext a b
    rfl
  have hΩ₀t : Ω₀ᵀ = -Ω₀ := by
    ext a b
    exact congrFun (congrFun hΩt a) b
  have hΩ₀det : Ω₀.det ≠ 0 := by
    intro h0
    apply hΩdet
    rw [← hΩ₀, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have h2₀ : (2 : h.fixedField) ≠ 0 := fun h0 => h2 (by
    have := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at this
    exact this)
  obtain ⟨P₀, hP₀⟩ := exists_symp_matrix4 h2₀ hΩ₀t hΩ₀det
  have hfix : ∀ x : h.fixedField, h.bar (x : K) = x := fun x => h.mem_fixedField.mp x.2
  set ι := h.fixedField.subtype with hι
  obtain ⟨P', hP'⟩ : ∃ P' : 𝕄₄, P' = (P₀ : Matrix (Fin 4) (Fin 4) h.fixedField).map ι :=
    ⟨_, rfl⟩
  have hP'bar : P'.map h.bar = P' := by
    ext a b
    rw [hP']
    exact hfix _
  have hGram : uadj h ((H : 𝕄₄) * P') * ((H : 𝕄₄) * P') =
      ω • (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] : 𝕄₄) := by
    have h1 : uadj h ((H : 𝕄₄) * P') * ((H : 𝕄₄) * P') = P'ᵀ * G * P' := by
      rw [uadj_mul, uadj, hP'bar, hG]
      simp only [uadj, Matrix.mul_assoc]
    have h2' : P'ᵀ * Ω * P' = (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] : 𝕄₄) := by
      rw [← hΩ₀, hP']
      have := congrArg (fun X : Matrix (Fin 4) (Fin 4) h.fixedField => X.map ι) hP₀
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      rw [this]
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    have hGΩ : G = ω • Ω := by rw [hΩ, smul_smul, mul_inv_cancel₀ hω0, one_smul]
    rw [h1, hGΩ, Matrix.mul_smul, Matrix.smul_mul, h2']
  set z : K := (2 * ω)⁻¹ with hz
  have hz2 : 2 * z * ω = 1 := by
    rw [hz]
    field_simp
  have hbz : h.bar z = -z := by
    rw [hz, map_inv₀, map_mul, hbω, map_ofNat h.bar 2, mul_neg, inv_neg]
  refine semi_assembly h (H := (H : 𝕄₄)) (P' := P')
    (Θ := !![1, i, 0, 0; z, -(i * z), 0, 0; 0, 0, 1, i; 0, 0, z, -(i * z)])
    (Ψ := !![0, i, 0, 0; -i, 0, 0, 0; 0, 0, 0, i; 0, 0, -i, 0]) (lam := -i) hH1 hP'bar ?_ ?_ ?_
  · rw [hGram]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [uadj, Matrix.mul_apply, Fin.sum_univ_four, hbi, hbz]
    all_goals first
      | ring1
      | linear_combination hz2
      | linear_combination (-(2 * z * ω)) * hi + hz2
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, hbi, hbz]
    all_goals first
      | ring1
      | linear_combination -hi
      | linear_combination z * hi
  · rw [coe_rot4]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four]

end CFSG.ClassicalInvolution.ModelFacts.L6C
