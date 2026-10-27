module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourRoots
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFour

open Matrix LinearFlag

variable {k : Type*} [Field k] [CharP k 2]

theorem exists_det_one_mul_eq (B : Matrix (Fin 3) (Fin 3) k) (hBB : B * B = 1) (hB1 : B ≠ 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) k, P.det = 1 ∧ B * P = P * wM 1 := by
  set N := B - 1 with hN
  have hNN : N * N = 0 := by
    rw [hN, sub_mul, mul_sub, mul_sub, hBB, mul_one, one_mul, one_mul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.zero_apply]
    linear_combination CharTwo.add_self_eq_zero ((1 : Matrix (Fin 3) (Fin 3) k) i j - B i j)
  have hN0 : N ≠ 0 := fun h => hB1 (sub_eq_zero.mp h)
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → k, N *ᵥ v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hN0 (ext_of_mulVec_single fun j => by rw [h, zero_mulVec])
  set u := N *ᵥ v with hu
  have hNu : N *ᵥ u = 0 := by rw [hu, mulVec_mulVec, hNN, zero_mulVec]
  set f := mulVecLin N with hf
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, hf, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, hNN, zero_mulVec]
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hdim
  have hmono := Submodule.finrank_mono hle
  have hspan : k ∙ u ≤ LinearMap.ker f := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hf, mulVecLin_apply]
    exact hNu
  have hlt : k ∙ u < LinearMap.ker f :=
    Submodule.lt_of_le_of_finrank_lt_finrank hspan (by rw [finrank_span_singleton hv]; omega)
  obtain ⟨w, hw, hwu⟩ := IsConcreteLE.exists_of_lt hlt
  have hNw : N *ᵥ w = 0 := by rwa [LinearMap.mem_ker, hf, mulVecLin_apply] at hw
  set M : Matrix (Fin 3) (Fin 3) k := Matrix.of fun i j => ![u, w, v] j i with hM
  have hMc : ∀ c : Fin 3 → k, M *ᵥ c = c 0 • u + c 1 • w + c 2 • v := by
    intro c
    ext i
    simp only [hM, mulVec, dotProduct, of_apply, Fin.sum_univ_three, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := exists_mulVec_eq_zero_iff.mpr h0
    rw [hMc] at hc
    have hc2 : c 2 = 0 := by
      have h := congrArg (fun x => N *ᵥ x) hc
      simp only [mulVec_add, mulVec_smul, hNu, hNw, ← hu, smul_zero, zero_add, mulVec_zero] at h
      exact (smul_eq_zero.mp h).resolve_right hv
    rw [hc2, zero_smul, add_zero] at hc
    have hc1 : c 1 = 0 := by
      by_contra h1
      apply hwu
      rw [Submodule.mem_span_singleton]
      refine ⟨-((c 1)⁻¹ * c 0), ?_⟩
      have hw' : w = (c 1)⁻¹ • (c 1 • w) := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
      rw [hw', eq_neg_of_add_eq_zero_right hc, smul_neg, smul_smul, neg_smul]
    rw [hc1, zero_smul, add_zero] at hc
    have hc0' : c 0 = 0 := (smul_eq_zero.mp hc).resolve_right hv
    exact hc0 (funext fun i => by fin_cases i <;> simp [hc0', hc1, hc2])
  obtain ⟨P, hPdet, hPc⟩ : ∃ P : Matrix (Fin 3) (Fin 3) k, P.det = 1 ∧
      ∀ c : Fin 3 → k, P *ᵥ c = c 0 • u + ((M.det)⁻¹ * c 1) • w + c 2 • v := by
    refine ⟨M * diagonal ![1, (M.det)⁻¹, 1], ?_, fun c => ?_⟩
    · rw [det_mul, det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, mul_one, one_mul]
      exact mul_inv_cancel₀ hdet
    · rw [← mulVec_mulVec, hMc]
      simp only [mulVec_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, one_mul]
  have hEc : ∀ c : Fin 3 → k, (wM (1 : k) - 1) *ᵥ c = ![c 2, 0, 0] := by
    intro c
    ext i
    fin_cases i <;> simp [wM, mulVec, dotProduct, Fin.sum_univ_three]
  have hE : N * P = P * (wM 1 - 1) := ext_of_mulVec_single fun j => by
    rw [← mulVec_mulVec (Pi.single j 1) N P, ← mulVec_mulVec (Pi.single j 1) P (wM 1 - 1), hPc,
      hEc, hPc]
    simp only [mulVec_add, mulVec_smul, hNu, hNw, ← hu, smul_zero, zero_add, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero,
      zero_smul, add_zero]
  refine ⟨P, hPdet, ?_⟩
  have hBN : B = N + 1 := by rw [hN, sub_add_cancel]
  calc B * P = N * P + P := by rw [hBN, add_mul, one_mul]
    _ = P * (wM 1 - 1) + P := by rw [hE]
    _ = P * wM 1 := by rw [mul_sub, mul_one, sub_add_cancel]

theorem exists_conj_eq_wMat_one (B : SpecialLinearGroup (Fin 3) k) (hB2 : B * B = 1)
    (hB1 : B ≠ 1) : ∃ g : SpecialLinearGroup (Fin 3) k, g * B * g⁻¹ = wMat 1 := by
  have hBB : (B : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k) = 1 :=
    congrArg Subtype.val hB2
  have hB1' : (B : Matrix (Fin 3) (Fin 3) k) ≠ 1 := fun h => hB1 (Subtype.ext h)
  obtain ⟨P, hPdet, hBP⟩ := exists_det_one_mul_eq (B : Matrix (Fin 3) (Fin 3) k) hBB hB1'
  let Q : SpecialLinearGroup (Fin 3) k := ⟨P, hPdet⟩
  have hQ : B * Q = Q * wMat 1 := Subtype.ext hBP
  refine ⟨Q⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, hQ, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_conj_eq_wP_one (y : projectiveSL 3 k) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ g : SpecialLinearGroup (Fin 3) k, proj 3 k g * y * (proj 3 k g)⁻¹ = wP 1 := by
  obtain ⟨B, rfl⟩ := proj_surjective 3 k y
  obtain ⟨c, hc3, hc⟩ := proj_eq_one_iff.mp (by rw [map_mul, hy2] : proj 3 k (B * B) = 1)
  obtain ⟨B₀, hB₀, hB₀2⟩ : ∃ B₀ : SpecialLinearGroup (Fin 3) k,
      proj 3 k B₀ = proj 3 k B ∧ B₀ * B₀ = 1 := by
    refine ⟨scalarElement c hc3 * B, ?_, ?_⟩
    · rw [map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars c hc3), one_mul]
    · apply Subtype.ext
      have hc' : (B : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k) =
          scalar (Fin 3) (c : k) := hc
      have hc3' : (c : k) * ((c : k) * c) = 1 := by
        rw [← pow_three, ← Units.val_pow_eq_pow_val, hc3, Units.val_one]
      change scalar (Fin 3) (c : k) * (B : Matrix (Fin 3) (Fin 3) k) *
        (scalar (Fin 3) (c : k) * (B : Matrix (Fin 3) (Fin 3) k)) = 1
      simp only [scalar_apply, ← smul_one_eq_diagonal, smul_mul_assoc, one_mul, mul_smul_comm,
        hc', smul_smul, hc3', one_smul]
  have hB₀1 : B₀ ≠ 1 := fun h => hy1 (by rw [← hB₀, h, map_one])
  obtain ⟨g, hg⟩ := exists_conj_eq_wMat_one B₀ hB₀2 hB₀1
  refine ⟨g, ?_⟩
  rw [← hB₀, wP, ← hg, map_mul, map_mul, map_inv]

end LinearFieldFour

end CFSG.LocalAnalysis.ComponentInitial
