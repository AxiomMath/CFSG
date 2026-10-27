module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviAut

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix
open scoped MatrixGroups

section Blocks

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι)

@[expose] noncomputable def oblk (Y : Matrix ι₂ ι₂ K)
    (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) : Matrix ι ι K :=
  reindexAlgEquiv K K oe (fromBlocks Y 0 0 X)

variable {oe}

theorem oblk_mul (Y Y' : Matrix ι₂ ι₂ K) (X X' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    oblk oe Y X * oblk oe Y' X' = oblk oe (Y * Y') (X * X') := by
  rw [oblk, oblk, oblk, ← map_mul, fromBlocks_multiply]
  simp

theorem oblk_one :
    oblk oe (1 : Matrix ι₂ ι₂ K) (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
  rw [oblk, fromBlocks_one, map_one]

theorem oblk_add (Y Y' : Matrix ι₂ ι₂ K) (X X' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    oblk oe Y X + oblk oe Y' X' = oblk oe (Y + Y') (X + X') := by
  rw [oblk, oblk, oblk, ← map_add, fromBlocks_add]
  simp

theorem oblk_smul (c : K) (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    c • oblk oe Y X = oblk oe (c • Y) (c • X) := by
  rw [oblk, oblk, ← map_smul, fromBlocks_smul]
  simp

theorem det_oblk (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (oblk oe Y X).det = Y.det * X.det := by
  rw [oblk, coe_reindexAlgEquiv, det_reindex_self, det_fromBlocks_zero₂₁]

theorem oblk_injective {Y Y' : Matrix ι₂ ι₂ K} {X X' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : oblk oe Y X = oblk oe Y' X') : Y = Y' ∧ X = X' := by
  rw [oblk, oblk] at h
  have h1 := (reindexAlgEquiv K K oe).injective h
  rw [fromBlocks_inj] at h1
  exact ⟨h1.1, h1.2.2.2⟩

theorem eq_reindex_fromBlocks_oe (g : Matrix ι ι K) :
    ∃ A B C D, g = reindexAlgEquiv K K oe (fromBlocks A B C D) := by
  set g' := (reindexAlgEquiv K K oe).symm g with hg'
  refine ⟨g'.toBlocks₁₁, g'.toBlocks₁₂, g'.toBlocks₂₁, g'.toBlocks₂₂, ?_⟩
  rw [fromBlocks_toBlocks, hg', AlgEquiv.apply_symm_apply]

theorem oblk_map_fun (g : K → K) (hg : g 0 = 0) (Y : Matrix ι₂ ι₂ K)
    (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (oblk oe Y X).map g = oblk oe (Y.map g) (X.map g) := by
  simp only [oblk, coe_reindexAlgEquiv, reindex_apply, ← submatrix_map, fromBlocks_map,
    Matrix.map_zero _ hg]

theorem transpose_oblk (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (oblk oe Y X)ᵀ = oblk oe Yᵀ Xᵀ := by
  rw [oblk, oblk, coe_reindexAlgEquiv, transpose_reindex, fromBlocks_transpose, transpose_zero]
  rfl

theorem oblk_mulVec_inl (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (v : ι → K) (a : ι₂) :
    (oblk oe Y X *ᵥ v) (oe (.inl a)) = (Y *ᵥ fun a' => v (oe (.inl a'))) a := by
  rw [oblk, coe_reindexAlgEquiv, reindex_apply, submatrix_mulVec_equiv]
  simp only [Function.comp, Equiv.symm_apply_apply]
  rw [fromBlocks_mulVec]
  simp [Sum.elim_inl, Matrix.zero_mulVec]
  rfl

theorem oblk_mulVec_inr (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (v : ι → K) (b : Fin 2 ⊕ Fin 2) :
    (oblk oe Y X *ᵥ v) (oe (.inr b)) = (X *ᵥ fun b' => v (oe (.inr b'))) b := by
  rw [oblk, coe_reindexAlgEquiv, reindex_apply, submatrix_mulVec_equiv]
  simp only [Function.comp, Equiv.symm_apply_apply]
  rw [fromBlocks_mulVec]
  simp [Sum.elim_inr, Matrix.zero_mulVec]
  rfl

@[expose] noncomputable def oblkMat (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) :
    GL ι₂ K × GL (Fin 2 ⊕ Fin 2) K →* Matrix ι ι K where
  toFun x := oblk oe (x.1 : Matrix ι₂ ι₂ K) (x.2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  map_one' := oblk_one
  map_mul' x y := by
    change oblk oe ((x.1 * y.1 : GL ι₂ K) : Matrix ι₂ ι₂ K)
      ((x.2 * y.2 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
    rw [Units.val_mul, Units.val_mul, ← oblk_mul]

variable (oe) in
@[expose] noncomputable def oblkGL : GL ι₂ K × GL (Fin 2 ⊕ Fin 2) K →* GL ι K :=
  (oblkMat oe).toHomUnits

theorem coe_oblkGL (x : GL ι₂ K × GL (Fin 2 ⊕ Fin 2) K) :
    ((oblkGL oe x : GL ι K) : Matrix ι ι K) =
      oblk oe (x.1 : Matrix ι₂ ι₂ K) (x.2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
  rfl

end Blocks

section Forms

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}

theorem quad_oblk_mulVec
    (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (v : ι → K) :
    Q (oblk oe Y X *ᵥ v) = Q₂ (Y *ᵥ fun a => v (oe (.inl a))) +
      StatedQuadPlus 2 K (X *ᵥ fun b => v (oe (.inr b))) := by
  rw [hQ]
  congr 2
  · funext a
    exact oblk_mulVec_inl Y X v a
  · funext b
    exact oblk_mulVec_inr Y X v b

theorem quad_oblk_mulVec_eq
    (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    {Y : Matrix ι₂ ι₂ K} {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hY : ∀ w, Q₂ (Y *ᵥ w) = Q₂ w) (hX : ∀ u, StatedQuadPlus 2 K (X *ᵥ u) = StatedQuadPlus 2 K u)
    (v : ι → K) : Q (oblk oe Y X *ᵥ v) = Q v := by
  rw [quad_oblk_mulVec hQ, hY, hX, hQ]

end Forms

section Rho

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] noncomputable def rhoTwoMat : SL(2, K) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun A := fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0
    (adjugate (A : Matrix (Fin 2) (Fin 2) K))ᵀ
  map_one' := by
    rw [Matrix.SpecialLinearGroup.coe_one, adjugate_one, transpose_one, fromBlocks_one]
  map_mul' A B := by
    rw [Matrix.SpecialLinearGroup.coe_mul, fromBlocks_multiply, adjugate_mul_distrib,
      transpose_mul]
    simp

@[expose] noncomputable def rhoOneMat : SL(2, K) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun B := fromBlocks ((B : Matrix (Fin 2) (Fin 2) K) 0 0 • 1)
    ((B : Matrix (Fin 2) (Fin 2) K) 0 1 • swapM) ((B : Matrix (Fin 2) (Fin 2) K) 1 0 • swapM)
    ((B : Matrix (Fin 2) (Fin 2) K) 1 1 • 1)
  map_one' := by
    simp [fromBlocks_one]
  map_mul' B B' := by
    rw [fromBlocks_multiply]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      swapM_mul_swapM, ← add_smul]
    congr 1 <;> ring_nf

theorem rhoTwoMat_apply (A : SL(2, K)) :
    rhoTwoMat A = fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0
      (adjugate (A : Matrix (Fin 2) (Fin 2) K))ᵀ :=
  rfl

theorem rhoOneMat_apply (B : SL(2, K)) :
    rhoOneMat B = fromBlocks ((B : Matrix (Fin 2) (Fin 2) K) 0 0 • 1)
      ((B : Matrix (Fin 2) (Fin 2) K) 0 1 • swapM) ((B : Matrix (Fin 2) (Fin 2) K) 1 0 • swapM)
      ((B : Matrix (Fin 2) (Fin 2) K) 1 1 • 1) :=
  rfl

theorem quadPlus_two_rhoTwo (A : SL(2, K)) (u : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K (rhoTwoMat A *ᵥ u) = StatedQuadPlus 2 K u := by
  have hdet := A.2
  rw [det_fin_two] at hdet
  simp only [StatedQuadPlus, Fin.sum_univ_two, rhoTwoMat_apply, mulVec, dotProduct,
    Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, adjugate_fin_two, transpose_apply, Matrix.zero_apply, zero_mul,
    add_zero, zero_add, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  linear_combination (u (.inl 0) * u (.inr 0) + u (.inl 1) * u (.inr 1)) * hdet

variable [CharP K 2]

theorem quadPlus_two_rhoOne (B : SL(2, K)) (u : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K (rhoOneMat B *ᵥ u) = StatedQuadPlus 2 K u := by
  have hdet := B.2
  rw [det_fin_two] at hdet
  simp only [StatedQuadPlus, Fin.sum_univ_two, rhoOneMat_apply, mulVec, dotProduct,
    Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul, swapM, Matrix.add_apply,
    single_apply, Matrix.one_apply]
  simp
  linear_combination (u (.inl 0) * u (.inr 0) + u (.inl 1) * u (.inr 1)) * hdet +
    ((B : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 1 0 *
      u (.inl 0) * u (.inl 1) + (B : Matrix (Fin 2) (Fin 2) K) 0 1 *
      (B : Matrix (Fin 2) (Fin 2) K) 1 1 * u (.inr 0) * u (.inr 1) +
      (B : Matrix (Fin 2) (Fin 2) K) 0 1 * (B : Matrix (Fin 2) (Fin 2) K) 1 0 *
      (u (.inl 0) * u (.inr 0) + u (.inl 1) * u (.inr 1))) * CharTwo.two_eq_zero (R := K)

theorem adjugate_transpose_eq (A : Matrix (Fin 2) (Fin 2) K) :
    (adjugate A)ᵀ = swapM * A * swapM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjugate_fin_two, swapM, Matrix.mul_apply, single_apply, CharTwo.neg_eq]

omit [CharP K 2] in
theorem swapM_mul_swapM_mul (X : Matrix (Fin 2) (Fin 2) K) : swapM * (swapM * X) = X := by
  rw [← Matrix.mul_assoc, swapM_mul_swapM, Matrix.one_mul]

omit [CharP K 2] in
theorem mul_swapM_mul_swapM (X : Matrix (Fin 2) (Fin 2) K) : X * swapM * swapM = X := by
  rw [Matrix.mul_assoc, swapM_mul_swapM, Matrix.mul_one]

theorem rhoOne_mul_rhoTwo (A B : SL(2, K)) :
    rhoOneMat B * rhoTwoMat A = rhoTwoMat A * rhoOneMat B := by
  rw [rhoOneMat_apply, rhoTwoMat_apply, fromBlocks_multiply, fromBlocks_multiply,
    adjugate_transpose_eq]
  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero, zero_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc, swapM_mul_swapM,
      mul_swapM_mul_swapM]

end Rho

section Omega

open CFSG.Assembly.LowTwoRank Subgroup

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}

theorem quad_mulVec_of_mem_closure {κ : Type} [Fintype κ] [DecidableEq κ] {R : (κ → K) → K}
    {M : GL κ K} (hM : M ∈ closure {A : GL κ K | ∀ v, R ((A : Matrix κ κ K) *ᵥ v) = R v})
    (v : κ → K) : R ((M : Matrix κ κ K) *ᵥ v) = R v := by
  induction hM using Subgroup.closure_induction generalizing v with
  | mem A hA => exact hA v
  | one => simp
  | mul A B _ _ hA hB => rw [Units.val_mul, ← mulVec_mulVec, hA, hB]
  | inv A _ hA =>
    have h1 := hA ((A⁻¹ : GL κ K) *ᵥ v)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h1
    exact h1.symm

theorem quad_mulVec_of_mem_statedOmega {κ : Type} [Fintype κ] [DecidableEq κ]
    {R : (κ → K) → K} {M : GL κ K} (hM : M ∈ StatedOmega R) (v : κ → K) :
    R ((M : Matrix κ κ K) *ᵥ v) = R v :=
  quad_mulVec_of_mem_closure (Subgroup.commutator_le_self _ hM) v

theorem mem_statedOmega_of_perfect {κ : Type} [Fintype κ] [DecidableEq κ] {R : (κ → K) → K}
    {G : Type*} [Group G] (hG : commutator G = ⊤) (φ : G →* GL κ K)
    (hφ : ∀ g, φ g ∈ closure {A : GL κ K | ∀ v, R ((A : Matrix κ κ K) *ᵥ v) = R v}) (g : G) :
    φ g ∈ StatedOmega R := by
  have h1 : g ∈ commutator G := by rw [hG]; trivial
  have h2 : φ g ∈ (commutator G).map φ := mem_map_of_mem φ h1
  have hle : (⊤ : Subgroup G).map φ ≤
      closure {A : GL κ K | ∀ v, R ((A : Matrix κ κ K) *ᵥ v) = R v} := by
    rintro _ ⟨x, -, rfl⟩
    exact hφ x
  rw [commutator_def, Subgroup.map_commutator] at h2
  exact commutator_mono hle hle h2

@[expose] noncomputable def oKappaGL : GL ι₂ K →* GL ι K := (oblkGL oe).comp (MonoidHom.inl _ _)

variable (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) +
  StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit hQ in
theorem coe_oKappaGL (Y : GL ι₂ K) :
    ((oKappaGL oe Y : GL ι K) : Matrix ι ι K) = oblk oe (Y : Matrix ι₂ ι₂ K) 1 :=
  rfl

theorem oKappaGL_mem {Y : GL ι₂ K} (hY : Y ∈ StatedOmega Q₂) :
    oKappaGL oe Y ∈ StatedOmega Q := by
  have hle : closure {Y : GL ι₂ K | ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w} ≤
      (closure {M : GL ι K | ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v}).comap (oKappaGL oe) := by
    rw [closure_le]
    intro Y hY
    exact subset_closure fun v => quad_oblk_mulVec_eq hQ hY (fun u => by simp) v
  have h2 : oKappaGL oe Y ∈ (StatedOmega Q₂).map (oKappaGL oe) := mem_map_of_mem _ hY
  unfold StatedOmega at h2 ⊢
  rw [Subgroup.map_commutator] at h2
  exact commutator_mono (map_le_iff_le_comap.mpr hle) (map_le_iff_le_comap.mpr hle) h2

@[expose] noncomputable def oKappa : StatedOmega Q₂ →* StatedOmega Q :=
  ((oKappaGL oe).comp (StatedOmega Q₂).subtype).codRestrict _ fun Y => oKappaGL_mem oe hQ Y.2

@[expose] noncomputable def oRhoTwoGL : SL(2, K) →* GL ι K :=
  (oblkGL oe).comp ((MonoidHom.inr _ _).comp rhoTwoMat.toHomUnits)

@[expose] noncomputable def oRhoOneGL : SL(2, K) →* GL ι K :=
  (oblkGL oe).comp ((MonoidHom.inr _ _).comp rhoOneMat.toHomUnits)

omit hQ in
theorem coe_oRhoTwoGL (A : SL(2, K)) :
    ((oRhoTwoGL oe A : GL ι K) : Matrix ι ι K) = oblk oe 1 (rhoTwoMat A) :=
  rfl

omit hQ in
theorem coe_oRhoOneGL (B : SL(2, K)) :
    ((oRhoOneGL oe B : GL ι K) : Matrix ι ι K) = oblk oe 1 (rhoOneMat B) :=
  rfl

theorem oRhoTwoGL_mem_closure (A : SL(2, K)) :
    oRhoTwoGL oe A ∈ closure {M : GL ι K | ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v} :=
  subset_closure fun v => quad_oblk_mulVec_eq hQ (fun w => by simp) (quadPlus_two_rhoTwo A) v

theorem oRhoOneGL_mem_closure [CharP K 2] (B : SL(2, K)) :
    oRhoOneGL oe B ∈ closure {M : GL ι K | ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v} :=
  subset_closure fun v => quad_oblk_mulVec_eq hQ (fun w => by simp) (quadPlus_two_rhoOne B) v

@[expose] noncomputable def oRhoTwo (hSL : commutator SL(2, K) = ⊤) : SL(2, K) →* StatedOmega Q :=
  (oRhoTwoGL oe).codRestrict _ (mem_statedOmega_of_perfect hSL _ (oRhoTwoGL_mem_closure oe hQ))

@[expose] noncomputable def oRhoOne [CharP K 2] (hSL : commutator SL(2, K) = ⊤) :
    SL(2, K) →* StatedOmega Q :=
  (oRhoOneGL oe).codRestrict _ (mem_statedOmega_of_perfect hSL _ (oRhoOneGL_mem_closure oe hQ))

end Omega

section Proj

open CFSG.Assembly.LowTwoRank Subgroup

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

variable (Q : (ι → K) → K) in
@[expose] noncomputable def oProj : StatedOmega Q →* StatedProj (StatedOmega Q) :=
  QuotientGroup.mk' _

theorem oProj_surjective (Q : (ι → K) → K) : Function.Surjective (oProj Q) :=
  QuotientGroup.mk'_surjective _

theorem oProj_injective [CharP K 2] {Q : (ι → K) → K} {v₀ : ι → K} (hv₀ : Q v₀ ≠ 0)
    (hsm : ∀ c : K, Q (c • v₀) = c * c * Q v₀) : Function.Injective (oProj Q) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker, oProj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have h1 := quad_mulVec_of_mem_statedOmega g.2 v₀
  have h2 : (diagonal fun _ => (c : K)) *ᵥ v₀ = (c : K) • v₀ := by
    funext i
    simp [mulVec_diagonal]
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, h2, hsm] at h1
  have h3 : (c : K) * c = 1 * 1 := by
    rw [one_mul]
    exact (mul_eq_right₀ hv₀).mp h1
  have hc1 : c = 1 := Units.ext (eq_of_mul_self_eq h3)
  rw [mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

end Proj

section Bars

open CFSG.Assembly.LowTwoRank Subgroup

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hSL : commutator SL(2, K) = ⊤)

@[expose] noncomputable def oBarTwo : Subgroup (StatedProj (StatedOmega Q)) :=
  ((oProj Q).comp (oRhoTwo oe hQ hSL)).range

@[expose] noncomputable def oBarOne : Subgroup (StatedProj (StatedOmega Q)) :=
  ((oProj Q).comp (oRhoOne oe hQ hSL)).range

@[expose] noncomputable def oBarL : Subgroup (StatedProj (StatedOmega Q)) :=
  ((oProj Q).comp (oKappa oe hQ)).range

variable {oe hQ hSL}

omit [CharP K 2] in
theorem coe_oRhoTwo (A : SL(2, K)) :
    (((oRhoTwo oe hQ hSL A : StatedOmega Q) : GL ι K) : Matrix ι ι K) = oblk oe 1 (rhoTwoMat A) :=
  rfl

theorem coe_oRhoOne (B : SL(2, K)) :
    (((oRhoOne oe hQ hSL B : StatedOmega Q) : GL ι K) : Matrix ι ι K) = oblk oe 1 (rhoOneMat B) :=
  rfl

omit [CharP K 2] in
theorem coe_oKappa (Y : StatedOmega Q₂) :
    (((oKappa oe hQ Y : StatedOmega Q) : GL ι K) : Matrix ι ι K) =
      oblk oe ((Y : GL ι₂ K) : Matrix ι₂ ι₂ K) 1 :=
  rfl

omit [CharP K 2] in
theorem oRhoTwo_commute_oKappa (A : SL(2, K)) (Y : StatedOmega Q₂) :
    oRhoTwo oe hQ hSL A * oKappa oe hQ Y = oKappa oe hQ Y * oRhoTwo oe hQ hSL A := by
  apply Subtype.ext
  apply Units.ext
  change oblk oe 1 (rhoTwoMat A) * oblk oe ((Y : GL ι₂ K) : Matrix ι₂ ι₂ K) 1 =
    oblk oe ((Y : GL ι₂ K) : Matrix ι₂ ι₂ K) 1 * oblk oe 1 (rhoTwoMat A)
  rw [oblk_mul, oblk_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]

theorem oRhoOne_commute_oKappa (B : SL(2, K)) (Y : StatedOmega Q₂) :
    oRhoOne oe hQ hSL B * oKappa oe hQ Y = oKappa oe hQ Y * oRhoOne oe hQ hSL B := by
  apply Subtype.ext
  apply Units.ext
  change oblk oe 1 (rhoOneMat B) * oblk oe ((Y : GL ι₂ K) : Matrix ι₂ ι₂ K) 1 =
    oblk oe ((Y : GL ι₂ K) : Matrix ι₂ ι₂ K) 1 * oblk oe 1 (rhoOneMat B)
  rw [oblk_mul, oblk_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]

theorem oRhoOne_commute_oRhoTwo (A B : SL(2, K)) :
    oRhoOne oe hQ hSL B * oRhoTwo oe hQ hSL A = oRhoTwo oe hQ hSL A * oRhoOne oe hQ hSL B := by
  apply Subtype.ext
  apply Units.ext
  change oblk oe 1 (rhoOneMat B) * oblk oe 1 (rhoTwoMat A) =
    oblk oe 1 (rhoTwoMat A) * oblk oe 1 (rhoOneMat B)
  rw [oblk_mul, oblk_mul, Matrix.one_mul, rhoOne_mul_rhoTwo]

omit [CharP K 2] in
theorem oBarTwo_commute_oBarL {x y : StatedProj (StatedOmega Q)} (hx : x ∈ oBarTwo oe hQ hSL)
    (hy : y ∈ oBarL oe hQ) : x * y = y * x := by
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, oRhoTwo_commute_oKappa]

theorem oBarOne_commute_oBarL {x y : StatedProj (StatedOmega Q)} (hx : x ∈ oBarOne oe hQ hSL)
    (hy : y ∈ oBarL oe hQ) : x * y = y * x := by
  obtain ⟨B, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, oRhoOne_commute_oKappa]

theorem oBarOne_commute_oBarTwo {x y : StatedProj (StatedOmega Q)} (hx : x ∈ oBarOne oe hQ hSL)
    (hy : y ∈ oBarTwo oe hQ hSL) : x * y = y * x := by
  obtain ⟨B, rfl⟩ := hx
  obtain ⟨A, rfl⟩ := hy
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, oRhoOne_commute_oRhoTwo]

omit [CharP K 2] in
theorem oRhoTwo_injective : Function.Injective (oRhoTwo oe hQ hSL) := by
  intro A A' h
  have h1 := congrArg (fun g : StatedOmega Q => ((g : GL ι K) : Matrix ι ι K)) h
  simp only [coe_oRhoTwo] at h1
  have h2 := (oblk_injective h1).2
  rw [rhoTwoMat_apply, rhoTwoMat_apply, fromBlocks_inj] at h2
  exact Subtype.ext h2.1

theorem oRhoOne_injective : Function.Injective (oRhoOne oe hQ hSL) := by
  intro B B' h
  have h1 := congrArg (fun g : StatedOmega Q => ((g : GL ι K) : Matrix ι ι K)) h
  simp only [coe_oRhoOne] at h1
  have h2 := (oblk_injective h1).2
  rw [rhoOneMat_apply, rhoOneMat_apply, fromBlocks_inj] at h2
  obtain ⟨e1, e2, e3, e4⟩ := h2
  have f1 := congrFun (congrFun e1 0) 0
  have f2 := congrFun (congrFun e2 0) 1
  have f3 := congrFun (congrFun e3 1) 0
  have f4 := congrFun (congrFun e4 0) 0
  simp [swapM] at f1 f2 f3 f4
  ext i j
  fin_cases i <;> fin_cases j
  · exact f1
  · exact f2
  · exact f3
  · exact f4

omit [CharP K 2] in
theorem oKappa_injective : Function.Injective (oKappa oe hQ) := by
  intro Y Y' h
  have h1 := congrArg (fun g : StatedOmega Q => ((g : GL ι K) : Matrix ι ι K)) h
  simp only [coe_oKappa] at h1
  exact Subtype.ext (Units.ext (oblk_injective h1).1)

end Bars

end CFSG.ComponentClassification.RankTwoClassical
