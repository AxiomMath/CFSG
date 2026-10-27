module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (rootElt rootElt_of_ne coe_rootElt_of_ne
  rootElt_add rootElt_zero)

variable {K : Type*} [Field K] {n k : ℕ}

section Corner

abbrev cornerEquiv (hk : k ≤ n) : Fin k ⊕ Fin (n - k) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))

theorem cornerEquiv_symm_of_lt (hk : k ≤ n) {i : Fin n} (hi : (i : ℕ) < k) :
    (cornerEquiv hk).symm i = Sum.inl ⟨i, hi⟩ := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [cornerEquiv]

theorem cornerEquiv_symm_of_le (hk : k ≤ n) {i : Fin n} (hi : k ≤ (i : ℕ)) :
    (cornerEquiv hk).symm i = Sum.inr ⟨i - k, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [cornerEquiv]
  omega

@[expose] def cornerMat (hk : k ≤ n) (A : Matrix (Fin k) (Fin k) K) : Matrix (Fin n) (Fin n) K :=
  (fromBlocks A 0 0 1).submatrix (cornerEquiv hk).symm (cornerEquiv hk).symm

theorem cornerMat_apply (hk : k ≤ n) (A : Matrix (Fin k) (Fin k) K) (i j : Fin n) :
    cornerMat hk A i j = if h : (i : ℕ) < k ∧ (j : ℕ) < k then A ⟨i, h.1⟩ ⟨j, h.2⟩
      else (1 : Matrix (Fin n) (Fin n) K) i j := by
  rw [cornerMat, submatrix_apply]
  by_cases hi : (i : ℕ) < k <;> by_cases hj : (j : ℕ) < k
  · rw [cornerEquiv_symm_of_lt hk hi, cornerEquiv_symm_of_lt hk hj, fromBlocks_apply₁₁]
    simp [hi, hj]
  · have hij : i ≠ j := fun h => by subst h; exact hj hi
    rw [cornerEquiv_symm_of_lt hk hi, cornerEquiv_symm_of_le hk (not_lt.mp hj),
      fromBlocks_apply₁₂, one_apply_ne hij]
    simp [hj]
  · have hij : i ≠ j := fun h => by subst h; exact hi hj
    rw [cornerEquiv_symm_of_le hk (not_lt.mp hi), cornerEquiv_symm_of_lt hk hj,
      fromBlocks_apply₂₁, one_apply_ne hij]
    simp [hi]
  · rw [cornerEquiv_symm_of_le hk (not_lt.mp hi), cornerEquiv_symm_of_le hk (not_lt.mp hj),
      fromBlocks_apply₂₂, dite_eq_right (fun h => hi h.1)]
    by_cases hij : i = j
    · subst hij
      simp
    · have hij' : (⟨(i : ℕ) - k, by omega⟩ : Fin (n - k)) ≠ ⟨(j : ℕ) - k, by omega⟩ := by
        intro h
        apply hij
        ext
        have h' := congrArg Fin.val h
        simp only at h'
        omega
      rw [one_apply_ne hij, one_apply_ne hij']

theorem cornerMat_mul (hk : k ≤ n) (A B : Matrix (Fin k) (Fin k) K) :
    cornerMat hk (A * B) = cornerMat hk A * cornerMat hk B := by
  rw [cornerMat, cornerMat, cornerMat, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem cornerMat_one (hk : k ≤ n) : cornerMat hk (1 : Matrix (Fin k) (Fin k) K) = 1 := by
  rw [cornerMat, fromBlocks_one, submatrix_one_equiv]

theorem cornerMat_transpose (hk : k ≤ n) (A : Matrix (Fin k) (Fin k) K) :
    (cornerMat hk A)ᵀ = cornerMat hk Aᵀ := by
  rw [cornerMat, cornerMat, transpose_submatrix, fromBlocks_transpose]
  simp

theorem cornerMat_map (hk : k ≤ n) (σ : K →+* K) (A : Matrix (Fin k) (Fin k) K) :
    (cornerMat hk A).map σ = cornerMat hk (A.map σ) := by
  rw [cornerMat, cornerMat, ← submatrix_map, fromBlocks_map]
  simp

theorem det_cornerMat (hk : k ≤ n) (A : Matrix (Fin k) (Fin k) K) :
    (cornerMat hk A).det = A.det := by
  rw [cornerMat, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]

@[expose] def cornerMatHom (hk : k ≤ n) : Matrix (Fin k) (Fin k) K →* Matrix (Fin n) (Fin n) K where
  toFun := cornerMat hk
  map_one' := cornerMat_one hk
  map_mul' := cornerMat_mul hk

@[expose] def cornerSL (hk : k ≤ n) :
    SpecialLinearGroup (Fin k) K →* SpecialLinearGroup (Fin n) K where
  toFun g := ⟨cornerMat hk g, by rw [det_cornerMat]; exact g.2⟩
  map_one' := by
    apply Subtype.ext
    change cornerMat hk ((1 : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, cornerMat_one]
  map_mul' g h := by
    apply Subtype.ext
    change cornerMat hk ((g * h : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      cornerMat hk g * cornerMat hk h
    rw [Matrix.SpecialLinearGroup.coe_mul, cornerMat_mul]

theorem coe_cornerSL (hk : k ≤ n) (g : SpecialLinearGroup (Fin k) K) :
    ((cornerSL hk g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      cornerMat hk g :=
  rfl

@[expose] def cornerGL (hk : k ≤ n) : GL (Fin k) K →* GL (Fin n) K :=
  Units.map (cornerMatHom hk)

theorem coe_cornerGL (hk : k ≤ n) (A : GL (Fin k) K) :
    ((cornerGL hk A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = cornerMat hk A :=
  rfl

theorem cornerSL_transpose (hk : k ≤ n) (g : SpecialLinearGroup (Fin k) K) :
    (cornerSL hk g).transpose = cornerSL hk g.transpose := by
  apply Subtype.ext
  change (cornerMat hk (g : Matrix (Fin k) (Fin k) K))ᵀ =
    cornerMat hk (g : Matrix (Fin k) (Fin k) K)ᵀ
  exact cornerMat_transpose hk _

theorem cornerSL_map (hk : k ≤ n) (σ : K →+* K) (g : SpecialLinearGroup (Fin k) K) :
    SpecialLinearGroup.map σ (cornerSL hk g) = cornerSL hk (SpecialLinearGroup.map σ g) := by
  apply Subtype.ext
  change (cornerMat hk (g : Matrix (Fin k) (Fin k) K)).map σ =
    cornerMat hk ((g : Matrix (Fin k) (Fin k) K).map σ)
  exact cornerMat_map hk σ _

theorem conjAut_cornerGL_proj_cornerSL (hk : k ≤ n) (A : GL (Fin k) K)
    (g : SpecialLinearGroup (Fin k) K) :
    conjAut n K (cornerGL hk A) (proj n K (cornerSL hk g)) =
      proj n K (cornerSL hk
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation k K A g)) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  change _ = cornerMat hk _
  rw [coe_slConjugation, coe_slConjugation, ← map_inv, coe_cornerGL, coe_cornerGL, coe_cornerSL,
    ← cornerMat_mul, ← cornerMat_mul]

theorem fieldAut_proj_cornerSL (hk : k ≤ n) (σ : K ≃+* K) (g : SpecialLinearGroup (Fin k) K) :
    fieldAut n K σ (proj n K (cornerSL hk g)) =
      proj n K (cornerSL hk (SpecialLinearGroup.map σ.toRingHom g)) := by
  rw [fieldAut_proj, cornerSL_map]

theorem dualAut_proj_cornerSL (hk : k ≤ n) (g : SpecialLinearGroup (Fin k) K) :
    dualAut n K (proj n K (cornerSL hk g)) = proj n K (cornerSL hk (g⁻¹).transpose) := by
  rw [dualAut_proj, ← map_inv, cornerSL_transpose]

theorem cornerSL_rootElt (hk : k ≤ n) {i j : Fin k} (hij : i ≠ j) (c : K) :
    cornerSL hk (rootElt i j c) =
      rootElt (⟨i, by omega⟩ : Fin n) ⟨j, by omega⟩ c := by
  have hij' : (⟨i, by omega⟩ : Fin n) ≠ ⟨j, by omega⟩ := fun h =>
    hij (Fin.ext (by simpa [Fin.ext_iff] using h))
  apply Subtype.ext
  change cornerMat hk _ = _
  rw [coe_rootElt_of_ne hij, coe_rootElt_of_ne hij']
  ext a b
  rw [cornerMat_apply]
  split_ifs with h
  · simp only [transvection, Matrix.add_apply, one_apply, single_apply, Fin.ext_iff]
  · have hab : ¬((i : ℕ) = a ∧ (j : ℕ) = b) := fun h' => h ⟨by omega, by omega⟩
    simp only [transvection, Matrix.add_apply, single_apply, Fin.ext_iff, hab, ite_false, add_zero]

end Corner

section SL2

@[expose] def fusionUpper (c : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, c; 0, 1], by simp [det_fin_two_of]⟩

@[expose] def fusionLower (c : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; c, 1], by simp [det_fin_two_of]⟩

@[expose] def fusionSwap [CharP K 2] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two_of, CharTwo.neg_eq]⟩

theorem coe_fusionUpper (c : K) :
    ((fusionUpper c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] :=
  rfl

theorem coe_fusionLower (c : K) :
    ((fusionLower c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] :=
  rfl

theorem coe_fusionSwap [CharP K 2] :
    ((fusionSwap : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
  rfl

theorem fusionUpper_eq_rootElt (c : K) : fusionUpper c = rootElt (0 : Fin 2) 1 c := by
  apply Subtype.ext
  change !![1, c; 0, 1] = _
  rw [coe_rootElt_of_ne (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [transvection]

theorem fusionLower_eq_rootElt (c : K) : fusionLower c = rootElt (1 : Fin 2) 0 c := by
  apply Subtype.ext
  change !![1, 0; c, 1] = _
  rw [coe_rootElt_of_ne (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [transvection]

theorem fusionSwap_eq [CharP K 2] :
    (fusionSwap : SpecialLinearGroup (Fin 2) K) =
      fusionLower 1 * fusionUpper 1 * fusionLower 1 := by
  apply Subtype.ext
  change !![0, 1; 1, 0] = !![1, 0; 1, 1] * !![1, 1; 0, 1] * !![1, 0; 1, 1]
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

end SL2

section Transvection

theorem isInvolutionClass_one_proj_rootElt [CharP K 2] {a b : Fin n} (hab : a ≠ b) :
    IsInvolutionClass 1 (proj n K (rootElt a b 1)) := by
  refine ⟨rootElt a b 1, rfl, ?_, ?_⟩
  · rw [← rootElt_add, CharTwo.add_self_eq_zero, rootElt_zero]
  · rw [coe_rootElt_of_ne hab, transvection, add_sub_cancel_left]
    have hcolb : (single a b (1 : K)).col b = Pi.single a 1 := by
      ext i
      simp [col_apply, single_apply, Pi.single_apply, eq_comm]
    refine rank_eq_one_of_col_mem (v := (Pi.single a (1 : K) : Fin n → K))
      (Pi.single_ne_zero_iff.mpr one_ne_zero) (fun j => ?_) hcolb
    by_cases hj : j = b
    · rw [hj, hcolb]
      exact Submodule.mem_span_singleton_self _
    · have h0 : (single a b (1 : K)).col j = 0 := by
        ext i
        simp [col_apply, Ne.symm hj]
      rw [h0]
      exact Submodule.zero_mem _

end Transvection

end CFSG.SeitzReduction.LinearPilot
