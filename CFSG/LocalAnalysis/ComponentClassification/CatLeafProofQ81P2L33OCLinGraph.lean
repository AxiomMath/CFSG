module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCTools
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_fixed_odd_conjAut_dualAut_of_basis {p : ℕ} [CharP K p] (hp : p.Prime)
    (hp2 : p ≠ 2) {ι : Type*} [Fintype ι] [DecidableEq ι] (A : GL (Fin n) K)
    (b : Basis ι K (Fin n → K)) {H : Type*} [Group H] {S : Set H} (hS : closure S = ⊤)
    (hSp : ∀ s ∈ S, s ^ p = 1) (Y : H →* GL ι K)
    (hY : ∀ h, ((Y h : GL ι K) : Matrix ι ι K)ᵀ *
      LinearMap.BilinForm.toMatrix b
        (toBilin' ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        (Y h : Matrix ι ι K) =
      LinearMap.BilinForm.toMatrix b
        (toBilin' ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (x : H) (hx4 : x ^ 4 = 1) (hxs : ∀ c : K, (Y x : Matrix ι ι K) ≠ scalar ι c) :
    ∃ T : Set (projectiveSL n K),
      (∀ t ∈ T, (conjAut n K A * dualAut n K) t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := by
  set R := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hR
  set B := toBilin' R with hB
  let ρ : H →* GL (Fin n) K :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm.toMonoidHom.comp
        ((basisMatrixEquiv b).symm.toMonoidHom.comp Y))
  have hρ : ∀ h, ((ρ h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      LinearMap.toMatrix' ((basisMatrixEquiv b).symm (Y h)).toLinearMap := fun h => rfl
  have hiso : ∀ h, (basisMatrixEquiv b).symm (Y h) ∈ isometryGroup B := fun h => by
    rw [isometry_iff_matrix b, MulEquiv.apply_symm_apply]
    exact hY h
  have hstd : ∀ h, ((ρ h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ * R *
      (ρ h : Matrix (Fin n) (Fin n) K) = R := fun h => by
    have h1 := (isometry_iff_matrix (Pi.basisFun K (Fin n)) B _).1 (hiso h)
    rw [basisMatrixEquiv_val, LinearMap.toMatrix_eq_toMatrix', hB,
      LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h1
    rw [hρ]
    exact h1
  refine exists_fixed_odd_of_hom hp hp2 hS hSp ρ _
    (fun g hg => conjAut_dualAut_proj_of_transpose_mul_mul A ⟨_, hg⟩ (hstd g)) x hx4 ?_
  intro c hc
  apply hxs c
  have hg : ((basisMatrixEquiv b).symm (Y x)).toLinearMap = c • LinearMap.id := by
    apply LinearMap.toMatrix'.injective
    rw [← hρ x, hc, map_smul, LinearMap.toMatrix'_id, scalar_apply, smul_one_eq_diagonal]
  conv_lhs => rw [← MulEquiv.apply_symm_apply (basisMatrixEquiv b) (Y x)]
  rw [basisMatrixEquiv_val, hg, map_smul, LinearMap.toMatrix_id, scalar_apply,
    smul_one_eq_diagonal]

theorem exists_fixed_odd_conjAut_dualAut_of_transpose_eq [Finite K] {p : ℕ} [CharP K p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = A) :
    ∃ T : Set (projectiveSL n K),
      (∀ t ∈ T, (conjAut n K A * dualAut n K) t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := by
  classical
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨m, rfl⟩ : ∃ m, n = 3 + m := ⟨n - 3, by omega⟩
  set R := ((A⁻¹ : GL (Fin (3 + m)) K) : Matrix (Fin (3 + m)) (Fin (3 + m)) K) with hR
  have hRt : Rᵀ = R := by
    have hAR : (A : Matrix (Fin (3 + m)) (Fin (3 + m)) K) * R = 1 := by
      rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : Rᵀ * (A : Matrix (Fin (3 + m)) (Fin (3 + m)) K)ᵀ = 1 := by
      rw [← transpose_mul, hR, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
    rw [hA] at h1
    calc Rᵀ = Rᵀ * ((A : Matrix (Fin (3 + m)) (Fin (3 + m)) K) * R) := by
          rw [hAR, Matrix.mul_one]
      _ = R := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hsymm : LinearMap.IsSymm (toBilin' R) := by
    refine LinearMap.isSymm_def.2 fun x y => ?_
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec, ← mulVec_transpose,
      hRt, dotProduct_comm]
    rfl
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  set b := v.reindex (finCongr (finrank_fin_fun K)) with hb
  have hbo : (toBilin' R).iIsOrtho b := fun i j hij => by
    change toBilin' R (b i) (b j) = 0
    rw [hb, Basis.reindex_apply, Basis.reindex_apply]
    exact hv (by simpa using hij)
  have hnd : (toBilin' R).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2
      (Matrix.isUnits_det_units A⁻¹).ne_zero
  set d : Fin (3 + m) → K := fun i => toBilin' R (b i) (b i) with hd
  have hd0 : ∀ i, d i ≠ 0 := hbo.not_isOrtho_basis_self_of_nondegenerate hnd
  have hG : LinearMap.BilinForm.toMatrix b (toBilin' R) = diagonal d := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, diagonal_apply]
    split_ifs with h
    · rw [h]
    · exact hbo h
  obtain ⟨ζ, hζ, hζs⟩ :=
    exists_ternary_isometry_hom hK (fun i => d (finSumFinEquiv (Sum.inl i))) fun i => hd0 _
  refine exists_fixed_odd_conjAut_dualAut_of_basis hp hp2 A b
    LinearGroups.special_linear_elementary_generation (fun s hs => elementary_pow_char hs)
    ((blockGL K 3 m).comp ζ) (fun X => ?_) (QuaternionMatrices.slQuatI K)
    QuaternionMatrices.slQuatI_pow_four fun c => blockGL_ne_scalar_of_ne_scalar hζs c
  rw [hG, diagonal_eq_diagBlock, MonoidHom.comp_apply, coe_blockGL_eq_diagBlock,
    diagBlock_transpose, diagBlock_mul, diagBlock_mul, hζ, transpose_one, Matrix.one_mul,
    Matrix.mul_one]

theorem exists_fixed_odd_conjAut_dualAut_of_transpose_eq_neg {p : ℕ} [CharP K p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = -A) :
    ∃ T : Set (projectiveSL n K),
      (∀ t ∈ T, (conjAut n K A * dualAut n K) t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := by
  classical
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  set R := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hR
  have hAR : (A : Matrix (Fin n) (Fin n) K) * R = 1 := by
    rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRt : Rᵀ = -R := by
    have h1 : Rᵀ * (A : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
      rw [← transpose_mul, hR, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
    rw [hA, Matrix.mul_neg, neg_eq_iff_eq_neg] at h1
    calc Rᵀ = Rᵀ * ((A : Matrix (Fin n) (Fin n) K) * R) := by rw [hAR, Matrix.mul_one]
      _ = -R := by rw [← Matrix.mul_assoc, h1, Matrix.neg_mul, Matrix.one_mul]
  have hBalt : (toBilin' R).IsAlt := fun v => by
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    rw [Matrix.toBilin'_apply']
    have hx : v ⬝ᵥ (R *ᵥ v) = -(v ⬝ᵥ (R *ᵥ v)) := by
      conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hRt, neg_mulVec, neg_dotProduct,
        dotProduct_comm]
    have h3 : (2 : K) * (v ⬝ᵥ (R *ᵥ v)) = 0 := by linear_combination hx
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hBnd : (toBilin' R).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2
      (Matrix.isUnits_det_units A⁻¹).ne_zero
  obtain ⟨k, b, hb⟩ := hBalt.exists_basis_toMatrix_eq_J hBnd
  have hk : n = k + k := by
    have h := Module.finrank_eq_card_basis b
    rwa [finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h
  obtain ⟨k', rfl⟩ : ∃ k', k = 2 + k' := ⟨k - 2, by omega⟩
  let Y : SpecialLinearGroup (Fin 2) K →* GL (Fin (2 + k') ⊕ Fin (2 + k')) K :=
    (TauCeti.GLSymplectic (Fin (2 + k')) K).subtype.comp
      (TauCeti.GLSymplectic.leviHom.comp ((blockGL K 2 k').comp SpecialLinearGroup.toGL))
  refine exists_fixed_odd_conjAut_dualAut_of_basis hp hp2 A b
    LinearGroups.special_linear_elementary_generation (fun s hs => elementary_pow_char hs) Y
    (fun h => ?_) (QuaternionMatrices.slQuatI K) QuaternionMatrices.slQuatI_pow_four ?_
  · rw [hb]
    exact TauCeti.GLSymplectic.mem_iff'.1 (TauCeti.GLSymplectic.leviHom _).2
  · intro c hc
    have hne : (Sum.inl (finSumFinEquiv (Sum.inl 1)) : Fin (2 + k') ⊕ Fin (2 + k')) ≠
        Sum.inl (finSumFinEquiv (Sum.inl 0)) := by
      simp
    have h1 := congrFun (congrFun hc (Sum.inl (finSumFinEquiv (Sum.inl 1))))
      (Sum.inl (finSumFinEquiv (Sum.inl 0)))
    change (((TauCeti.GLSymplectic.leviHom (blockGL K 2 k'
      (SpecialLinearGroup.toGL (QuaternionMatrices.slQuatI K))) :
        TauCeti.GLSymplectic (Fin (2 + k')) K) : GL (Fin (2 + k') ⊕ Fin (2 + k')) K) :
          Matrix (Fin (2 + k') ⊕ Fin (2 + k')) (Fin (2 + k') ⊕ Fin (2 + k')) K) _ _ = _ at h1
    rw [TauCeti.GLSymplectic.coe_leviHom, fromBlocks_apply₁₁, blockGL_apply_inl, scalar_apply,
      diagonal_apply_ne _ hne] at h1
    change QuaternionMatrices.quatI K 1 0 = 0 at h1
    simp [QuaternionMatrices.quatI] at h1

end CFSG.ComponentClassification.HarrisLit.L33.OC
