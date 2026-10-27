module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.CubicFrame
public import CFSG.HardMathSupport.Lang.Proving.HermitianIsotropic
public import CFSG.HardMathSupport.Lang.Proving.CubeNormOne
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K]

theorem irred_core (h : UnitaryFieldData p f K) (ω l ν : K) (hω3 : ω ^ 3 = 1)
    (hωb : h.bar ω * ω = 1) (Bm Q : Matrix (Fin 3) (Fin 3) K) (hν : ν ≠ 0)
    (hQQ : (Q.map h.bar)ᵀ * Q = ν • (1 : Matrix (Fin 3) (Fin 3) K))
    (hBQ : Bm * Q = Q * !![0, 0, l; 1, 0, 0; 0, 1, 0]) :
    ∃ H : Matrix (Fin 3) (Fin 3) K, (H.map h.bar)ᵀ * H = 1 ∧ H.det = 1 ∧ H ^ 3 = 1 ∧
      Bm * H = ω⁻¹ • (H * Bm) := by
  classical
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hinv : ω⁻¹ = ω ^ 2 := by
    field_simp
    linear_combination -hω3
  set C : Matrix (Fin 3) (Fin 3) K := !![0, 0, l; 1, 0, 0; 0, 1, 0] with hC
  set D : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, ω, ω ^ 2] with hD
  set D' : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal (fun i => h.bar (![1, ω, ω ^ 2] i)) with hD'
  set cj : Matrix (Fin 3) (Fin 3) K → Matrix (Fin 3) (Fin 3) K := fun X => (X.map h.bar)ᵀ with hcj
  have cj_mul : ∀ X Y, cj (X * Y) = cj Y * cj X := by
    intro X Y
    simp [hcj, Matrix.map_mul, Matrix.transpose_mul]
  have cj_smul : ∀ (a : K) X, cj (a • X) = h.bar a • cj X := by
    intro a X
    ext i j
    simp [hcj]
  have cj_cj : ∀ X, cj (cj X) = X := by
    intro X
    ext i j
    simp [hcj, h.bar_bar]
  have cj_D : cj D = D' := by
    simp [hcj, hD, hD', Matrix.diagonal_map]
  set Qh := cj Q with hQh
  have hQQ' : Qh * Q = ν • (1 : Matrix (Fin 3) (Fin 3) K) := hQQ
  have hνb : h.bar ν = ν := by
    have e1 : cj (Qh * Q) = Qh * Q := by
      rw [cj_mul]
      have : cj Qh = Q := cj_cj Q
      rw [this]
    have e2 := congrArg cj hQQ'
    rw [e1, cj_smul, hQQ'] at e2
    have h00 := congrFun (congrFun e2 0) 0
    have e3 : cj (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by simp [hcj]
    rw [e3] at h00
    simpa using h00.symm
  set c : K := ν⁻¹ with hc
  have hcν : c * ν = 1 := inv_mul_cancel₀ hν
  have hcb : h.bar c = c := by rw [hc, map_inv₀, hνb]
  have hQc : Q * (c • Qh) = 1 := by
    apply mul_eq_one_comm.1
    rw [Matrix.smul_mul, hQQ', smul_smul, hcν, one_smul]
  have hQQh : Q * Qh = ν • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have : Q * Qh = ν • (Q * (c • Qh)) := by
      rw [Matrix.mul_smul, smul_smul, mul_comm ν c, hcν, one_smul]
    rw [this, hQc]
  set ψ : Matrix (Fin 3) (Fin 3) K → Matrix (Fin 3) (Fin 3) K := fun X => c • (Q * X * Qh) with hψ
  have hmul : ∀ X Y, ψ X * ψ Y = ψ (X * Y) := by
    intro X Y
    simp only [hψ, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : Q * X * Qh * (Q * Y * Qh) = ν • (Q * (X * Y) * Qh) := by
      calc Q * X * Qh * (Q * Y * Qh) = Q * X * (Qh * Q) * Y * Qh := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hQQ']
          simp [Matrix.mul_assoc]
    rw [this, smul_smul]
    have e : c * c * ν = c := by rw [mul_assoc, hcν, mul_one]
    rw [e]
  have hψ1 : ψ 1 = 1 := by
    simp only [hψ, Matrix.mul_one]
    rw [hQQh, smul_smul, hcν, one_smul]
  have hD3 : D * D * D = 1 := by
    simp only [hD, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp <;> first | linear_combination hω3 | linear_combination (ω ^ 3 + 1) * hω3
  have hDD : D' * D = 1 := by
    simp only [hD, hD', Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
    · exact hωb
    · linear_combination (h.bar ω * ω + 1) * hωb
  have hCD : C * D = ω⁻¹ • (D * C) := by
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hC, hD, Matrix.mul_apply, Matrix.diagonal_apply] <;>
      first | ring1 | linear_combination (-1) * hω3 | linear_combination (-ω) * hω3
  have hQhB : Qh * Bm = C * Qh := by
    have : Qh * Bm = Qh * Bm * (Q * (c • Qh)) := by rw [hQc, Matrix.mul_one]
    rw [this]
    calc Qh * Bm * (Q * (c • Qh)) = Qh * (Bm * Q) * (c • Qh) := by simp only [Matrix.mul_assoc]
      _ = (Qh * Q) * C * (c • Qh) := by rw [hBQ]; simp only [Matrix.mul_assoc]
      _ = C * Qh := by
        rw [hQQ']
        simp [smul_smul, hcν]
  refine ⟨ψ D, ?_, ?_, ?_, ?_⟩
  · have e : cj (ψ D) = ψ D' := by
      simp only [hψ]
      rw [cj_smul, hcb, cj_mul, cj_mul, hQh, cj_cj, cj_D]
      simp only [Matrix.mul_assoc]
    show cj (ψ D) * ψ D = 1
    rw [e, hmul, hDD, hψ1]
  · simp only [hψ]
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, hD, Matrix.det_diagonal]
    have h1 : Q.det * Qh.det = ν ^ 3 := by
      rw [← Matrix.det_mul, hQQh, Matrix.det_smul, Matrix.det_one]
      simp
    simp only [Fin.prod_univ_three]
    simp
    calc c ^ 3 * (Q.det * (ω * ω ^ 2) * Qh.det) = (c * ν) ^ 3 * ω ^ 3 := by
          linear_combination (c ^ 3 * ω ^ 3) * h1
      _ = 1 := by rw [hcν, hω3]; simp
  · have : ψ D ^ 3 = ψ (D * D * D) := by
      rw [pow_succ, pow_succ, pow_one, hmul, hmul]
    rw [this, hD3, hψ1]
  · simp only [hψ]
    calc Bm * (c • (Q * D * Qh)) = c • (Bm * Q * D * Qh) := by
          simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = c • (Q * (C * D) * Qh) := by rw [hBQ]; simp only [Matrix.mul_assoc]
      _ = ω⁻¹ • (c • (Q * D * (C * Qh))) := by
          rw [hCD]
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm c, Matrix.mul_assoc]
      _ = ω⁻¹ • ((c • (Q * D * Qh)) * Bm) := by
          rw [← hQhB]
          simp only [Matrix.smul_mul, Matrix.mul_assoc]

theorem irred_frame (h : UnitaryFieldData p f K) (Bm : Matrix (Fin 3) (Fin 3) K)
    (hB : (Bm.map h.bar)ᵀ * Bm = 1) {l : K}
    (hB3 : Bm ^ 3 = l • (1 : Matrix (Fin 3) (Fin 3) K)) (hl : ∀ x : K, x ^ 3 ≠ l) :
    ∃ (Q : Matrix (Fin 3) (Fin 3) K) (ν : K), ν ≠ 0 ∧
      (Q.map h.bar)ᵀ * Q = ν • (1 : Matrix (Fin 3) (Fin 3) K) ∧
      Bm * Q = Q * !![0, 0, l; 1, 0, 0; 0, 1, 0] := by
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨w, hw0, hw⟩ := CFSG.HardMathSupport.Lang.Proving.exists_ne_zero_bar_dotProduct_mulVec_eq_zero
    (K := K) (p := p) (f := f) h.card h.one_le (le_refl 3) Bm
  have e01 : hpair h w (Bm *ᵥ w) = 0 := by
    simpa [hpair, dotProduct, h.bar_apply] using hw
  have e02 : hpair h w ((Bm ^ 2) *ᵥ w) = 0 := by
    have := hpair_pow_pow (h := h) hB w w 1 3
    simp only [show (1 : ℕ) ≤ 3 by norm_num, ↓reduceIte, pow_one] at this
    rw [pow_three_mulVec hB3, hpair_smul_right,
      hpair_comm w (Bm *ᵥ w), e01, map_zero, mul_zero] at this
    simpa using this.symm
  set ν : K := hpair h w w with hνdef
  have e12 : hpair h (Bm *ᵥ w) ((Bm ^ 2) *ᵥ w) = 0 := by
    have := hpair_pow_pow (h := h) hB w w 1 2
    simp only [show (1 : ℕ) ≤ 2 by norm_num, ↓reduceIte, pow_one] at this
    simpa [e01] using this
  have e11 : hpair h (Bm *ᵥ w) (Bm *ᵥ w) = ν := hpair_mulVec hB w w
  have e22 : hpair h ((Bm ^ 2) *ᵥ w) ((Bm ^ 2) *ᵥ w) = ν := hpair_pow_shift hB 2 w w
  have e10 : hpair h (Bm *ᵥ w) w = 0 := by rw [hpair_comm, e01, map_zero]
  have e20 : hpair h ((Bm ^ 2) *ᵥ w) w = 0 := by rw [hpair_comm, e02, map_zero]
  have e21 : hpair h ((Bm ^ 2) *ᵥ w) (Bm *ᵥ w) = 0 := by rw [hpair_comm, e12, map_zero]
  set Q : Matrix (Fin 3) (Fin 3) K := (Matrix.of ![w, Bm *ᵥ w, (Bm ^ 2) *ᵥ w])ᵀ with hQ
  have hQQ : (Q.map h.bar)ᵀ * Q = ν • (1 : Matrix (Fin 3) (Fin 3) K) := by
    ext j k
    have key : ((Q.map h.bar)ᵀ * Q) j k = hpair h (![w, Bm *ᵥ w, (Bm ^ 2) *ᵥ w] j)
        (![w, Bm *ᵥ w, (Bm ^ 2) *ᵥ w] k) := by
      simp [Matrix.mul_apply, hpair, hQ]
    rw [key]
    fin_cases j <;> fin_cases k <;> simp [e01, e02, e12, e10, e20, e21, e11, e22, hνdef]
  have hdet : Q.det ≠ 0 := by
    have hli := cyc_linearIndependent Bm hB3 hl hw0
    have hcol : Q.col = ![w, Bm *ᵥ w, (Bm ^ 2) *ᵥ w] := by
      ext j i
      fin_cases j <;> simp [hQ]
    have hu : IsUnit Q := Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
    exact (Matrix.isUnit_iff_isUnit_det Q).1 hu |>.ne_zero
  refine ⟨Q, ν, ?_, hQQ, ?_⟩
  · intro hν0
    have h1 := congrArg Matrix.det hQQ
    rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hν0] at h1
    simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h1
    rw [zero_pow (by norm_num)] at h1
    rcases mul_eq_zero.1 h1 with h1 | h1
    · exact hdet ((map_eq_zero h.bar).1 h1)
    · exact hdet h1
  · have hc0 : Bm *ᵥ w = ![w, Bm *ᵥ w, (Bm ^ 2) *ᵥ w] 1 := rfl
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

theorem exists_irred_element (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1)
    (B : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) {l : K}
    (hB3 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = l • (1 : Matrix (Fin 3) (Fin 3) K))
    (hl : ∀ x : K, x ^ 3 ≠ l) :
    ∃ (ω : K) (H : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
      ω ^ 3 = 1 ∧ ω ≠ 1 ∧ h.bar ω * ω = 1 ∧ (H : GL (Fin 3) K) ^ 3 = 1 ∧
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((H : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ω⁻¹ • (((H : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  classical
  have hB : (((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := mem_primeFormUnitary.1 B.2
    simpa using this
  obtain ⟨Q, ν, hν, hQQ, hBQ⟩ := irred_frame h _ hB hB3 hl
  have hfin := h.finite
  obtain ⟨ω, hω3, hω1, -, hωq⟩ := CFSG.HardMathSupport.Lang.Proving.exists_primitive_cube_root_normOne
    (K := K) (q := p ^ f) (by rw [h.card, pow_mul']) h3
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hωb : h.bar ω * ω = 1 := by
    rw [h.bar_apply, hωq, inv_mul_cancel₀ hω0]
  obtain ⟨H, hHu, hHdet, hH3, hBH⟩ := irred_core h ω l ν hω3 hωb _ Q hν hQQ hBQ
  let Hu : GL (Fin 3) K := ⟨H, H ^ 2, by rw [← pow_succ', hH3], by rw [← pow_succ, hH3]⟩
  have hHu' : ((Hu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = H := rfl
  refine ⟨ω, ⟨Hu, ?_, ?_⟩, hω3, hω1, hωb, ?_, ?_⟩
  · rw [hHu']
    simpa using hHu
  · rw [hHu']; exact hHdet
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hHu', hH3, Units.val_one]
  · show _ * H = _ • (H * _)
    exact hBH

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
