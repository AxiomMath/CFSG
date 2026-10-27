module

public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowHom
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionPaired
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_orthonormal_pair (h : UnitaryFieldData p f K) {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    {W : Submodule K V} (hW : (B.domRestrict₁₂ W W).SeparatingLeft) (h2 : 2 ≤ finrank K W) :
    ∃ v₁ ∈ W, ∃ v₂ ∈ W, B v₁ v₁ = 1 ∧ B v₂ v₂ = 1 ∧ B v₁ v₂ = 0 := by
  have hBW : (B.domRestrict₁₂ W W).IsSymm := ⟨fun x y => hB.eq x y⟩
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hBW hW
  have h0 := he ⟨0, by omega⟩ ⟨0, by omega⟩
  have h1 := he ⟨1, by omega⟩ ⟨1, by omega⟩
  have h01 := he ⟨0, by omega⟩ ⟨1, by omega⟩
  simp only [LinearMap.domRestrict₁₂_apply] at h0 h1
  simp only [LinearMap.domRestrict₁₂_apply, Fin.mk.injEq, zero_ne_one, ite_false] at h01
  exact ⟨_, (e ⟨0, by omega⟩).2, _, (e ⟨1, by omega⟩).2, h0, h1, h01⟩

section Operator

variable {r ε : ℕ}

theorem gram_colMat_eq_hypForm (h : UnitaryFieldData p f K) {κ : Type*}
    (v : κ → HypIndex r ε → K) :
    ((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v =
      Matrix.of fun i j => hypForm h r ε (v i) (v j) :=
  gram_colMat _ _ _

@[expose] noncomputable def unitaryOfHyp (h : UnitaryFieldData p f K) {A : GL (HypIndex r ε) K}
    (hA : A ∈ hypUnitary h r ε) : sesqUnitaryGroup (hypForm h r ε) :=
  ⟨GeneralLinearGroup.toLin A, fun x y => by
    rw [GeneralLinearGroup.coe_toLin, mulVecLin_apply, mulVecLin_apply, gramForm_mulVec,
      mem_hypUnitary.mp hA]⟩

theorem coe_unitaryOfHyp (h : UnitaryFieldData p f K) {A : GL (HypIndex r ε) K}
    (hA : A ∈ hypUnitary h r ε) :
    (((unitaryOfHyp h hA : sesqUnitaryGroup (hypForm h r ε)) :
      LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) : Module.End K (HypIndex r ε → K)) =
      mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K) :=
  GeneralLinearGroup.coe_toLin A

theorem mulVecLin_mul_self {A : Matrix (HypIndex r ε) (HypIndex r ε) K} {l : K}
    (hAA : A * A = (l ^ 2) • 1) : mulVecLin A * mulVecLin A = (l ^ 2) • 1 := by
  refine LinearMap.ext fun v => ?_
  rw [Module.End.mul_apply, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, hAA, smul_mulVec,
    one_mulVec]
  rfl

theorem mulVec_eq_of_mem_eigenPlus {A : Matrix (HypIndex r ε) (HypIndex r ε) K} {l : K}
    (hl0 : l ≠ 0) {v : HypIndex r ε → K} (hv : v ∈ eigenPlus l (mulVecLin A)) :
    A *ᵥ v = l • v := by
  have h1 := apply_eq_of_mem_ker_sub_one hv
  rw [invSMulOp, LinearMap.smul_apply, mulVecLin_apply] at h1
  rw [← h1, smul_smul, mul_inv_cancel₀ hl0, one_smul, h1]

theorem mulVec_eq_of_mem_eigenMinus {A : Matrix (HypIndex r ε) (HypIndex r ε) K} {l : K}
    (hl0 : l ≠ 0) {v : HypIndex r ε → K} (hv : v ∈ eigenMinus l (mulVecLin A)) :
    A *ᵥ v = (-l) • v := by
  have h1 := apply_eq_neg_of_mem_ker_add_one hv
  rw [invSMulOp, LinearMap.smul_apply, mulVecLin_apply] at h1
  have h2 : A *ᵥ v = l • (l⁻¹ • A *ᵥ v) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  rw [h2, h1, smul_neg, neg_smul]

end Operator

section Split

variable {r ε : ℕ}

theorem exists_orthonormal_eigen_pair (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {l : K}
    (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1)
    (hN : h.norm l = 1) :
    ∃ d : K, h.norm d = 1 ∧ ∃ v₁ v₂ : HypIndex r ε → K,
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v₁ = d • v₁ ∧
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v₂ = d • v₂ ∧
      hypForm h r ε v₁ v₁ = 1 ∧ hypForm h r ε v₂ v₂ = 1 ∧ hypForm h r ε v₁ v₂ = 0 := by
  have hAA' := mulVecLin_mul_self hAA
  rw [← coe_unitaryOfHyp h hA] at hAA'
  obtain ⟨-, hsepP, hsepM, -⟩ := exists_split_centralizer_equiv hp (hypForm_isSymm h)
    (hypForm_separatingLeft h) hl0 hAA' hN
  rw [coe_unitaryOfHyp] at hsepP hsepM hAA'
  have hc : IsCompl (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K)))
      (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) :=
    isCompl_ker_sub_one_ker_add_one (two_ne_zero_of_odd h hp) (invSMulOp_mul_self hl0 hAA')
  have hdim := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_hypIndex_fun] at hdim
  by_cases hP : 2 ≤ finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε)
    (HypIndex r ε) K)))
  · obtain ⟨v₁, hv₁, v₂, hv₂, h1, h2, h12⟩ := exists_orthonormal_pair h (hypForm_isSymm h)
      hsepP hP
    exact ⟨l, hN, v₁, v₂, mulVec_eq_of_mem_eigenPlus hl0 hv₁,
      mulVec_eq_of_mem_eigenPlus hl0 hv₂, h1, h2, h12⟩
  · have hM : 2 ≤ finrank K (eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε)
        (HypIndex r ε) K))) := by
      omega
    obtain ⟨v₁, hv₁, v₂, hv₂, h1, h2, h12⟩ := exists_orthonormal_pair h (hypForm_isSymm h)
      hsepM hM
    refine ⟨-l, ?_, v₁, v₂, mulVec_eq_of_mem_eigenMinus hl0 hv₁,
      mulVec_eq_of_mem_eigenMinus hl0 hv₂, h1, h2, h12⟩
    rw [UnitaryFieldData.norm, map_neg, neg_mul_neg]
    exact hN

theorem exists_norm_eq_neg_one (h : UnitaryFieldData p f K) : ∃ c : K, h.norm c = -1 := by
  have hm : (-1 : K) ∈ h.fixedField := by rw [h.mem_fixedField, map_neg, map_one]
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨-1, hm⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem exists_bar_eq_neg (h : UnitaryFieldData p f K) : ∃ t : K, t ≠ 0 ∧ h.bar t = -t := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  exact ⟨c - h.bar c, sub_ne_zero.mpr (Ne.symm hc), by rw [map_sub, h.bar_bar, neg_sub]⟩

theorem exists_comm_planeHom_of_norm_eq_one (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {l : K}
    (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1)
    (hN : h.norm l = 1) :
    ∃ ψ : SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ c : K, ((ψ (QuaternionMatrices.slQuatI h.fixedField) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) ≠ c • 1 := by
  obtain ⟨d, hd, v₁, v₂, hAv₁, hAv₂, h11, h22, h12⟩ :=
    exists_orthonormal_eigen_pair h hp hn hA hl0 hAA hN
  obtain ⟨c, hc⟩ := exists_norm_eq_neg_one h
  obtain ⟨t, ht0, ht⟩ := exists_bar_eq_neg h
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp
  have h2t : 2 * t ≠ 0 := mul_ne_zero h2 ht0
  have hB := hypForm_isSymm (r := r) (ε := ε) h
  have h21 : hypForm h r ε v₂ v₁ = 0 := by rw [← hB.eq v₁ v₂, h12, map_zero]
  have hcN : c * h.bar c = -1 := hc
  have htN : h.bar t = -t := ht
  obtain ⟨u, hu⟩ : ∃ u : HypIndex r ε → K, u = v₁ + c • v₂ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : HypIndex r ε → K, w = t • (v₁ - c • v₂) := ⟨_, rfl⟩
  have hUU : hypForm h r ε u u = 0 := by
    simp only [hu, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
      h11, h22, h12, h21]
    linear_combination hcN
  have hUW : hypForm h r ε u w = 2 * t := by
    simp only [hu, hw, map_add, map_sub, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul,
      smul_eq_mul, h11, h22, h12, h21]
    linear_combination (-t) * hcN
  have hWU : hypForm h r ε w u = -(2 * t) := by
    simp only [hu, hw, map_add, map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul,
      smul_eq_mul, h11, h22, h12, h21]
    linear_combination (1 - h.bar c * c) * htN + t * hcN
  have hWW : hypForm h r ε w w = 0 := by
    simp only [hw, map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
      h11, h22, h12, h21]
    linear_combination (h.bar t * t) * hcN
  have hAu : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ u = d • u := by
    rw [hu, mulVec_add, mulVec_smul, hAv₁, hAv₂, smul_add, smul_comm c d]
  have hAw : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w = d • w := by
    rw [hw, mulVec_smul, mulVec_sub, mulVec_smul, hAv₁, hAv₂, smul_sub, smul_comm c d, smul_sub,
      smul_sub, smul_comm t d, smul_comm t d]
  set E : Matrix (HypIndex r ε) (Fin 2) K := colMat ![u, w] with hE
  have hG : (E.map h.bar)ᵀ * hypGram r ε K * E = (2 * t) • QuaternionMatrices.quatI K := by
    rw [hE, gram_colMat_eq_hypForm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [QuaternionMatrices.quatI, hUU, hUW, hWU, hWW]
  set Gi : Matrix (Fin 2) (Fin 2) K := -(2 * t)⁻¹ • QuaternionMatrices.quatI K with hGi
  have hGiG : Gi * ((E.map h.bar)ᵀ * hypGram r ε K * E) = 1 := by
    rw [hG, hGi, smul_mul_smul_comm, QuaternionMatrices.quatI_mul_self, neg_mul,
      inv_mul_cancel₀ h2t, neg_smul, one_smul, neg_neg]
  have hGGi : ((E.map h.bar)ᵀ * hypGram r ε K * E) * Gi = 1 := by
    rw [hG, hGi, smul_mul_smul_comm, QuaternionMatrices.quatI_mul_self, mul_neg,
      mul_inv_cancel₀ h2t, neg_smul, one_smul, neg_neg]
  obtain ⟨ψ, hψ⟩ := exists_hypSU_hom h hGiG hGGi (planeHom h)
    (fun x => by rw [hG]; exact planeHom_isometry h _ x) (det_planeHom h)
  have hFE : Gi * (E.map h.bar)ᵀ * hypGram r ε K * E = 1 := by
    rw [← hGiG]
    simp only [Matrix.mul_assoc]
  have hAE : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * E =
      E * (d • (1 : Matrix (Fin 2) (Fin 2) K)) := by
    rw [hE, mul_colMat, colMat_mul_smul_one]
    congr 1
    funext i
    fin_cases i
    · exact hAu
    · exact hAw
  have hFA := suppF_mul_of_isometry (mem_hypUnitary.mp hA) hAE hGiG hGGi
  refine ⟨ψ, fun x => ?_, fun c' hc' => ?_⟩
  · rw [hψ]
    refine mul_suppMat hAE hFA ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · rw [hψ] at hc'
    have h3 := eq_smul_one_of_suppMat hFE hc'
    rw [planeHom_slQuatI] at h3
    exact quatI_ne_smul_one c' h3

end Split

section Paired

variable {r ε : ℕ}

theorem exists_paired_eigen_basis (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 4 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {l : K}
    (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1)
    (hN : h.norm l = -1) :
    ∃ e f : Fin 2 → HypIndex r ε → K,
      (∀ i, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ e i = l • e i) ∧
      (∀ i, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ f i = (-l) • f i) ∧
      (∀ i j, hypForm h r ε (e i) (e j) = 0) ∧ (∀ i j, hypForm h r ε (f i) (f j) = 0) ∧
      ∀ i j, hypForm h r ε (e i) (f j) = if i = j then 1 else 0 := by
  have hAA' := mulVecLin_mul_self hAA
  rw [← coe_unitaryOfHyp h hA] at hAA'
  obtain ⟨hisoP, hisoM, hdimeq, h2dim, -, hpairMP, -⟩ := exists_paired_centralizer_equiv hp
    (hypForm_isSymm h) (hypForm_separatingLeft h) hl0 hAA' hN
  rw [coe_unitaryOfHyp] at hisoP hisoM hdimeq h2dim hpairMP
  rw [finrank_hypIndex_fun] at h2dim
  set Vp := eigenPlus l (mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) with hVp
  set Vm := eigenMinus l (mulVecLin (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) with hVm
  have hm2 : 2 ≤ finrank K Vp := by omega
  set b := Module.finBasis K Vp with hb
  set Λ : Vm →ₗ[K] (Fin (finrank K Vp) → K) :=
    LinearMap.pi fun i => (hypForm h r ε (b i : HypIndex r ε → K)).comp Vm.subtype with hΛdef
  have hΛ : ∀ w i, Λ w i = hypForm h r ε (b i : HypIndex r ε → K) w := fun _ _ => rfl
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine Subtype.ext (hpairMP _ w.2 fun v hv => ?_)
    have hv' : v = ∑ i, (b.repr ⟨v, hv⟩ i) • (b i : HypIndex r ε → K) := by
      have := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hv', map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ₂, ← hΛ, hw, Pi.zero_apply, smul_zero]
  have hsurj : Function.Surjective Λ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun, ← hdimeq])).mp hinj
  choose g hg using fun j : Fin (finrank K Vp) => hsurj (Pi.single j 1)
  refine ⟨fun i => b (Fin.castLE hm2 i), fun j => g (Fin.castLE hm2 j), fun i => ?_, fun i => ?_,
    fun i j => hisoP _ (b _).2 _ (b _).2, fun i j => hisoM _ (g _).2 _ (g _).2, fun i j => ?_⟩
  · exact mulVec_eq_of_mem_eigenPlus hl0 (b _).2
  · exact mulVec_eq_of_mem_eigenMinus hl0 (g _).2
  · rw [← hΛ, hg, Pi.single_apply]
    simp only [Fin.castLE_inj]

theorem colMat_mul_fromBlocks {ι : Type*} (v : Fin 2 ⊕ Fin 2 → ι → K) (a b : K) :
    colMat v * (fromBlocks (a • 1) 0 0 (b • 1) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      colMat (Sum.elim (fun i => a • v (.inl i)) fun i => b • v (.inr i)) := by
  ext x i
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  rcases i with i | i <;>
    simp [colMat, fromBlocks, one_apply, mul_comm]

theorem exists_comm_pairHom_of_norm_eq_neg_one (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 4 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {l : K}
    (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1)
    (hN : h.norm l = -1) :
    ∃ ψ : SpecialLinearGroup (Fin 2) K →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ c : K, ((ψ (QuaternionMatrices.slQuatI K) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) ≠ c • 1 := by
  obtain ⟨e, f, hAe, hAf, hee, hff, hef⟩ := exists_paired_eigen_basis h hp hn hA hl0 hAA hN
  have hfe : ∀ i j, hypForm h r ε (f i) (e j) = if i = j then 1 else 0 := fun i j => by
    rw [← (hypForm_isSymm h).eq (e j) (f i), hef]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  set E : Matrix (HypIndex r ε) (Fin 2 ⊕ Fin 2) K := colMat (Sum.elim e f) with hE
  set G₄ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 1 0 with hG₄
  have hG : (E.map h.bar)ᵀ * hypGram r ε K * E = G₄ := by
    rw [hE, gram_colMat_eq_hypForm, hG₄]
    ext (i | i) (j | j) <;> simp [hee, hff, hef, hfe, one_apply]
  have hGG : G₄ * G₄ = 1 := by
    rw [hG₄, fromBlocks_multiply]
    simp [fromBlocks_one]
  have hGiG : G₄ * ((E.map h.bar)ᵀ * hypGram r ε K * E) = 1 := by rw [hG, hGG]
  have hGGi : ((E.map h.bar)ᵀ * hypGram r ε K * E) * G₄ = 1 := by rw [hG, hGG]
  obtain ⟨ψ, hψ⟩ := exists_hypSU_hom h hGiG hGGi (pairHom h)
    (fun x => by rw [hG, hG₄]; exact pairHom_isometry h x) (det_pairHom h)
  have hFE : G₄ * (E.map h.bar)ᵀ * hypGram r ε K * E = 1 := by
    rw [← hGiG]
    simp only [Matrix.mul_assoc]
  have hAE : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * E =
      E * (fromBlocks (l • 1) 0 0 ((-l) • 1) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [hE, mul_colMat, colMat_mul_fromBlocks]
    congr 1
    funext i
    rcases i with i | i
    · exact hAe i
    · exact hAf i
  have hFA := suppF_mul_of_isometry (mem_hypUnitary.mp hA) hAE hGiG hGGi
  refine ⟨ψ, fun x => ?_, fun c hc => ?_⟩
  · rw [hψ]
    exact mul_suppMat hAE hFA (pairHom_comm h l x)
  · rw [hψ] at hc
    exact pairHom_slQuatI_ne_smul_one h c (eq_smul_one_of_suppMat hFE hc)

end Paired

end CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
