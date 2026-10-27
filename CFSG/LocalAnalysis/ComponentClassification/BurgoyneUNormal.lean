module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLNormal
public import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherHermitian

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.PSL (signMat isCompl_ker_of_sq_one)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem stdHermForm_eq_dotProduct (x y : Fin n → K) :
    stdHermForm h n x y = (fun i => h.bar (x i)) ⬝ᵥ y := rfl

theorem stdHermForm_mulVec {A : Matrix (Fin n) (Fin n) K} (hA : (A.map h.bar)ᵀ * A = 1)
    (x y : Fin n → K) : stdHermForm h n (A *ᵥ x) (A *ᵥ y) = stdHermForm h n x y := by
  rw [stdHermForm_eq_dotProduct, stdHermForm_eq_dotProduct]
  have e : (fun i => h.bar ((A *ᵥ x) i)) = (A.map h.bar) *ᵥ (fun i => h.bar (x i)) := by
    funext i
    simp only [mulVec, dotProduct, map_sum, map_mul, map_apply]
  rw [e, ← vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, hA, vecMul_one]

theorem exists_split_unitary_normal_form (h2 : (2 : K) ≠ 0) {A : Matrix (Fin n) (Fin n) K}
    (hA : (A.map h.bar)ᵀ * A = 1) (hAA : A * A = 1) :
    ∃ (H : Matrix (Fin n) (Fin n) K) (J : Finset (Fin n)), (H.map h.bar)ᵀ * H = 1 ∧
      A * H = H * signMat K J := by
  set T := Matrix.toLin' A with hT
  have hTT : T * T = 1 := by
    rw [hT, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hAA, Matrix.toLin'_one]
    rfl
  set Vp := LinearMap.ker (T - 1) with hVp
  set Vm := LinearMap.ker (T + 1) with hVm
  have hc : IsCompl Vp Vm := isCompl_ker_of_sq_one h2 hTT
  have hp : ∀ v ∈ Vp, A *ᵥ v = v := by
    intro v hv
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  have hm : ∀ v ∈ Vm, A *ᵥ v = -v := by
    intro v hv
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hv
    exact eq_neg_of_add_eq_zero_left hv
  set B := stdHermForm h n with hB
  have horth : ∀ v ∈ Vp, ∀ w ∈ Vm, B v w = 0 := by
    intro v hv w hw
    have e := stdHermForm_mulVec h hA v w
    rw [hp v hv, hm w hw, map_neg] at e
    have : (2 : K) * B v w = 0 := by linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left h2
  have horth' : ∀ v ∈ Vp, ∀ w ∈ Vm, B w v = 0 := by
    intro v hv w hw
    rw [← (stdHermForm_isSymm h n).eq, horth v hv w hw, map_zero]
  have hsep : ∀ (W W' : Submodule K (Fin n → K)), IsCompl W W' →
      (∀ v ∈ W, ∀ w ∈ W', B v w = 0) → (B.domRestrict₁₂ W W).SeparatingLeft := by
    intro W W' hWW' hWo v hv
    apply Subtype.ext
    apply stdHermForm_separatingLeft h n
    intro x
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hWW'.sup_eq_top ▸ Submodule.mem_top :
      x ∈ W ⊔ W')
    rw [map_add, hWo v v.2 z hz, add_zero]
    exact hv ⟨y, hy⟩
  have hsepP := hsep Vp Vm hc horth
  have hsepM := hsep Vm Vp hc.symm fun v hv w hw => horth' w hw v hv
  obtain ⟨ep, hep⟩ := h.exists_orthonormal_basis ((stdHermForm_isSymm h n).domRestrict Vp)
    hsepP
  obtain ⟨em, hem⟩ := h.exists_orthonormal_basis ((stdHermForm_isSymm h n).domRestrict Vm)
    hsepM
  have hsum : Module.finrank K Vp + Module.finrank K Vm = n := by
    rw [Submodule.finrank_add_eq_of_isCompl hc, Module.finrank_fin_fun]
  set c : Fin (Module.finrank K Vp) ⊕ Fin (Module.finrank K Vm) → (Fin n → K) :=
    Sum.elim (fun i => (ep i : Fin n → K)) (fun i => (em i : Fin n → K)) with hcdef
  have hcB : ∀ x y, B (c x) (c y) = if x = y then 1 else 0 := by
    rintro (i | i) (j | j)
    · have e := hep i j
      rw [LinearMap.domRestrict₁₂_apply] at e
      simpa [hcdef, hB] using e
    · simpa [hcdef] using horth _ (ep i).2 _ (em j).2
    · simpa [hcdef] using horth' _ (ep j).2 _ (em i).2
    · have e := hem i j
      rw [LinearMap.domRestrict₁₂_apply] at e
      simpa [hcdef, hB] using e
  set σ : Fin (Module.finrank K Vp) ⊕ Fin (Module.finrank K Vm) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr hsum) with hσ
  set H : Matrix (Fin n) (Fin n) K := Matrix.of fun i l => c (σ.symm l) i with hH
  refine ⟨H, Finset.univ.filter fun l => (σ.symm l).isRight, ?_, ?_⟩
  · ext l l'
    have e := hcB (σ.symm l) (σ.symm l')
    rw [hB, stdHermForm_apply] at e
    rw [Matrix.mul_apply, one_apply]
    simp only [transpose_apply, map_apply, hH, of_apply]
    rw [e]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  · ext i l
    rw [signMat, mul_diagonal]
    have hAc : ∀ x, A *ᵥ c x = (if x.isRight then (-1 : K) else 1) • c x := by
      rintro (j | j)
      · simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte, one_smul]
        exact hp _ (ep j).2
      · simp only [Sum.isRight_inr, ↓reduceIte, neg_smul, one_smul]
        exact hm _ (em j).2
    have e := congrFun (hAc (σ.symm l)) i
    have e2 : (A * H) i l = (A *ᵥ c (σ.symm l)) i := by
      rw [Matrix.mul_apply, mulVec, dotProduct]
      rfl
    rw [e2, e]
    simp only [Pi.smul_apply, smul_eq_mul, hH, of_apply, Finset.mem_filter, Finset.mem_univ,
      true_and]
    split_ifs <;> ring

end CFSG.ComponentClassification.Burgoyne.U
