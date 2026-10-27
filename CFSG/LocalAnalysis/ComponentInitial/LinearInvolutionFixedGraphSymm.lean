module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools
public import CFSG.LocalAnalysis.ComponentInitial.QuadraticLowDimensionTraceZero
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroAction
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module CFSG.ComponentClassification.CatalogueBOrthogonal

variable {n : ℕ} {K : Type*} [Field K]

theorem eq_of_dotProduct_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (h2 : (2 : K) ≠ 0)
    {S T : Matrix ι ι K} (hS : Sᵀ = S) (hT : Tᵀ = T)
    (h : ∀ v : ι → K, v ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ (T *ᵥ v)) : S = T := by
  set U := S - T with hU
  have hUt : Uᵀ = U := by rw [hU, transpose_sub, hS, hT]
  have hq : ∀ v : ι → K, v ⬝ᵥ (U *ᵥ v) = 0 := fun v => by
    rw [hU, sub_mulVec, dotProduct_sub, h, sub_self]
  have hentry : ∀ i j, Pi.single i 1 ⬝ᵥ (U *ᵥ Pi.single j 1) = U i j := fun i j => by
    rw [mulVec_single_one, single_one_dotProduct]
    rfl
  rw [← sub_eq_zero]
  ext i j
  have h1 := hq (Pi.single i 1 + Pi.single j 1)
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hentry, hentry, hentry, hentry,
    show U i i = 0 by rw [← hentry]; exact hq _, show U j j = 0 by rw [← hentry]; exact hq _,
    show U j i = U i j by rw [← transpose_apply U i j, hUt]] at h1
  have h3 : (2 : K) * U i j = 0 := by linear_combination h1
  rw [Matrix.zero_apply]
  exact (mul_eq_zero.1 h3).resolve_left h2

theorem diagonal_eq_diagBlock {k m : ℕ} (d : Fin (k + m) → K) :
    diagonal d = diagBlock (diagonal fun i => d (finSumFinEquiv (Sum.inl i)))
      (diagonal fun j => d (finSumFinEquiv (Sum.inr j))) := by
  rw [diagBlock, fromBlocks_diagonal, reindex_apply, submatrix_diagonal_equiv]
  congr 1
  funext i
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  rcases a with a | a <;> simp

theorem exists_ternary_isometry_hom [Finite K] (hK : ringChar K ≠ 2) (d : Fin 3 → K)
    (hd : ∀ i, d i ≠ 0) :
    ∃ ζ : SpecialLinearGroup (Fin 2) K →* GL (Fin 3) K,
      (∀ X, ((ζ X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * diagonal d *
        (ζ X : Matrix (Fin 3) (Fin 3) K) = diagonal d) ∧
      ∀ c : K, (ζ (QuaternionMatrices.slQuatI K) : Matrix (Fin 3) (Fin 3) K) ≠
        scalar (Fin 3) c := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Odd (Nat.card K) := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hK
  set D := diagonal d with hD
  set Q : QuadraticForm K (Fin 3 → K) := (toBilin' D).toQuadraticMap with hQ
  have hQv : ∀ v, Q v = v ⬝ᵥ (D *ᵥ v) := fun v => by
    rw [hQ, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply']
  have hDt : Dᵀ = D := diagonal_transpose d
  have hpol : Q.polarBilin = toBilin' ((2 : K) • D) := by
    rw [hQ, LinearMap.BilinMap.polarBilin_toQuadraticMap]
    refine LinearMap.ext₂ fun x y => ?_
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.flip_apply, Matrix.toBilin'_apply',
      Matrix.toBilin'_apply', Matrix.toBilin'_apply', smul_mulVec, dotProduct_smul,
      dotProduct_mulVec y, ← mulVec_transpose, hDt, dotProduct_comm (D *ᵥ y), two_smul]
  have hQnd : Q.polarBilin.Nondegenerate := by
    rw [hpol]
    refine LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 ?_
    rw [det_smul, det_diagonal]
    exact mul_ne_zero (pow_ne_zero _ h2) (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  obtain ⟨-, -, c₀, ψ, -, hψ, -, -, -⟩ :=
    odd_three_space_trace_zero_similarity hodd Q hQnd (finrank_fin_fun K)
  let cψ : (traceZeroSubmodule K ≃ₗ[K] traceZeroSubmodule K) →*
      ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :=
    { toFun := fun h => ψ.trans (h.trans ψ.symm)
      map_one' := LinearEquiv.ext fun v => by simp
      map_mul' := fun h h' => LinearEquiv.ext fun v => by simp }
  let ζ : SpecialLinearGroup (Fin 2) K →* GL (Fin 3) K :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 3 → K)).symm.toMonoidHom.comp
        (cψ.comp ((TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)).subtype.comp
          (traceZeroOrthogonalAction.comp SpecialLinearGroup.toGL))))
  have hζv : ∀ X v, (ζ X : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      ψ.symm ((traceZeroOrthogonalAction (SpecialLinearGroup.toGL X)).val (ψ v)) := fun X v => by
    change toLin' (LinearMap.toMatrix' _) v = _
    rw [Matrix.toLin'_toMatrix']
    rfl
  refine ⟨ζ, fun X => ?_, fun c hc => ?_⟩
  · set M := (ζ X : Matrix (Fin 3) (Fin 3) K) with hM
    have hiso : ∀ v, Q (M *ᵥ v) = Q v := fun v => by
      rw [hM, hζv, hψ, hψ, LinearEquiv.apply_symm_apply, ← traceZeroForm_eq_neg_det,
        ← traceZeroForm_eq_neg_det,
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (traceZeroOrthogonalAction _).2]
    refine eq_of_dotProduct_mulVec_eq h2 ?_ hDt fun v => ?_
    · rw [transpose_mul, transpose_mul, transpose_transpose, hDt, Matrix.mul_assoc]
    · rw [← hQv, ← hiso, hQv]
      conv_lhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  · set g := SpecialLinearGroup.toGL (QuaternionMatrices.slQuatI K) with hg
    have hact : ∀ w : traceZeroSubmodule K, (traceZeroOrthogonalAction g).val w = c • w :=
      fun w => by
        have h1 := hζv (QuaternionMatrices.slQuatI K) (ψ.symm w)
        rw [hc, LinearEquiv.apply_symm_apply] at h1
        apply ψ.symm.injective
        rw [← h1, map_smul, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec]
    have hginv : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] := by
      rw [hg, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix,
        QuaternionMatrices.coe_slQuatI_inv]
    have hgval : (g : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl
    have hY₁ : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) ∈ traceZeroSubmodule K := by
      rw [traceZeroSubmodule, LinearMap.mem_ker, Matrix.traceLinearMap_apply,
        Matrix.trace_fin_two]
      simp
    have hY₂ : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) ∈ traceZeroSubmodule K := by
      rw [traceZeroSubmodule, LinearMap.mem_ker, Matrix.traceLinearMap_apply,
        Matrix.trace_fin_two]
      simp
    have h₁ := congrArg (fun w : traceZeroSubmodule K => w.val 0 0) (hact ⟨_, hY₁⟩)
    have h₂ := congrArg (fun w : traceZeroSubmodule K => w.val 0 1) (hact ⟨_, hY₂⟩)
    simp only [traceZeroOrthogonalAction_val, Submodule.coe_smul, Matrix.smul_apply,
      smul_eq_mul] at h₁ h₂
    rw [hginv, hgval] at h₁ h₂
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h₁ h₂
    have h3 : (2 : K) = 0 := by linear_combination h₂ - h₁
    exact h2 h3

theorem exists_fixed_perfect_even_conjAut_dualAut_of_transpose_eq [Finite K]
    (hK : ringChar K ≠ 2) (h4 : ∃ s : Finset K, s.card = 4) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = A) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, (conjAut n K A * dualAut n K) s = s := by
  classical
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
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
  refine exists_fixed_perfect_even_conjAut_dualAut_of_basis A b ((blockGL K 3 m).comp ζ)
    (fun X => ?_) (QuaternionMatrices.slQuatI K) QuaternionMatrices.slQuatI_pow_four
    fun c => blockGL_ne_scalar_of_ne_scalar hζs c
  rw [hG, diagonal_eq_diagBlock, MonoidHom.comp_apply, coe_blockGL_eq_diagBlock,
    diagBlock_transpose, diagBlock_mul, diagBlock_mul, hζ, transpose_one, Matrix.one_mul,
    Matrix.mul_one]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
