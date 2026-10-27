module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

section XMat

variable {K : Type} [Field K]

@[expose] def onesM : Matrix (Fin 2) (Fin 2) K := !![1, 1; 1, 1]

theorem onesM_ne_zero : (onesM : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [onesM] at this

theorem transpose_one_add_smul_onesM (c : K) :
    (1 + c • (onesM : Matrix (Fin 2) (Fin 2) K))ᵀ = 1 + c • onesM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [onesM]

theorem map_one_add_smul_onesM {F : Type*} [FunLike F K K] [RingHomClass F K K] (φ : F) (c : K) :
    (1 + c • (onesM : Matrix (Fin 2) (Fin 2) K)).map φ = 1 + φ c • onesM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [onesM]

variable [CharP K 2]

theorem det_one_add_smul_onesM (c : K) : (1 + c • (onesM : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
  rw [det_fin_two]
  simp [onesM]
  ring_nf
  rw [CharTwo.two_eq_zero, mul_zero, add_zero]

theorem one_add_smul_onesM_mul_self (c : K) :
    (1 + c • (onesM : Matrix (Fin 2) (Fin 2) K)) * (1 + c • onesM) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [onesM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [CharTwo.two_eq_zero]

end XMat

section General

variable {K : Type} [Field K]

theorem map_swapM_of {F : Type*} [FunLike F K K] [RingHomClass F K K] (φ : F) :
    (swapM : Matrix (Fin 2) (Fin 2) K).map φ = swapM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM]

theorem map_twJ_of {F : Type*} [FunLike F K K] [RingHomClass F K K] (φ : F) (ζ : K) :
    (twJ ζ).map φ = twJ (φ ζ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twJ, map_inv₀]

theorem blk_map_one_right (τ : K ≃+* K) {k : ℕ} (X : Matrix (Fin 2) (Fin 2) K) :
    (blk X (1 : Matrix (Fin k) (Fin k) K)).map τ = blk (X.map τ) 1 := by
  rw [blk_map_fun _ (map_zero τ), Matrix.map_one _ (map_zero τ) (map_one τ)]

theorem blk_map_one_left (τ : K ≃+* K) {k : ℕ} (S : Matrix (Fin k) (Fin k) K) :
    (blk (1 : Matrix (Fin 2) (Fin 2) K) S).map τ = blk 1 (S.map τ) := by
  rw [blk_map_fun _ (map_zero τ), Matrix.map_one _ (map_zero τ) (map_one τ)]

theorem blk_apply_inl {k : ℕ} (X : Matrix (Fin 2) (Fin 2) K) (S : Matrix (Fin k) (Fin k) K)
    (i j : Fin 2) :
    blk X S (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = X i j := by
  rw [blk, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, fromBlocks_apply₁₁]

theorem apply_eq_of_mul_permMatrix_swap {n : ℕ} {M : Matrix (Fin n) (Fin n) K} {i j : Fin n}
    (h : M * (Equiv.swap i j).permMatrix K = (Equiv.swap i j).permMatrix K * M) :
    M i i = M j j := by
  have h1 := congrArg (fun N : Matrix (Fin n) (Fin n) K => N i j) h
  simpa [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
    using h1

theorem permMatrix_swap_mul_self {n : ℕ} (i j : Fin n) :
    (Equiv.swap i j).permMatrix K * (Equiv.swap i j).permMatrix K = 1 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext r t
  simp [PEquiv.toMatrix_apply, Matrix.one_apply, Equiv.swap_apply_self]

theorem exists_statedSU_eq_of_bar {f : ℕ} (h : UnitaryFieldData 2 f K) {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} (hdet : M.det = 1) (hu : (M.map h.bar)ᵀ * M = 1) :
    ∃ g : StatedSU n (2 ^ f) K, (g : GL (Fin n) K).val = M := by
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero), ?_⟩, rfl⟩
  exact (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mpr ⟨hdet, hu⟩

end General

section Fix

variable {K : Type} [Field K] [CharP K 2] {k f : ℕ} {τ : K ≃+* K} {A : GL (Fin (2 + k)) K}
  {α : MulAut (StatedProj (StatedSU (2 + k) (2 ^ f) K))}
  (hα : ∀ g : StatedSU (2 + k) (2 ^ f) K,
    ∃ hg : A * glAut τ (g : GL (Fin (2 + k)) K) * A⁻¹ ∈ StatedSU (2 + k) (2 ^ f) K,
      α (uProj K (2 + k) f g) = uProj K (2 + k) f ⟨_, hg⟩)
include hα

omit [CharP K 2] in
theorem exists_scalar_of_fix {g : StatedSU (2 + k) (2 ^ f) K}
    (hfix : α (uProj K (2 + k) f g) = uProj K (2 + k) f g) :
    ∃ c : Kˣ, (g : GL (Fin (2 + k)) K).val * A.val =
      (c : K) • (A.val * (g : GL (Fin (2 + k)) K).val.map τ) := by
  obtain ⟨hg, hαg⟩ := hα g
  rw [hfix] at hαg
  obtain ⟨c, hc⟩ := uProj_eq_uProj_iff.mp hαg.symm
  refine ⟨c, ?_⟩
  have h1 : (g : GL (Fin (2 + k)) K) * A =
      GeneralLinearGroup.scalar (Fin (2 + k)) c * A * glAut τ (g : GL (Fin (2 + k)) K) :=
    calc (g : GL (Fin (2 + k)) K) * A = GeneralLinearGroup.scalar (Fin (2 + k)) c *
          (A * glAut τ (g : GL (Fin (2 + k)) K) * A⁻¹) * A := by rw [← hc]
      _ = _ := by group
  have h2 := congrArg Units.val h1
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_glAut] at h2
  rw [h2, Matrix.mul_assoc, scalar_apply, ← smul_eq_diagonal_mul]

theorem mul_eq_of_fix {g : StatedSU (2 + k) (2 ^ f) K} (hg2 : g * g = 1)
    (hfix : α (uProj K (2 + k) f g) = uProj K (2 + k) f g) :
    A.val * (g : GL (Fin (2 + k)) K).val.map τ = (g : GL (Fin (2 + k)) K).val * A.val := by
  obtain ⟨hg, hαg⟩ := hα g
  rw [hfix] at hαg
  have hsq : (⟨_, hg⟩ : StatedSU (2 + k) (2 ^ f) K) * ⟨_, hg⟩ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    calc A * glAut τ (g : GL (Fin (2 + k)) K) * A⁻¹ * (A * glAut τ (g : GL (Fin (2 + k)) K) * A⁻¹)
        = A * (glAut τ (g : GL (Fin (2 + k)) K) * glAut τ (g : GL (Fin (2 + k)) K)) * A⁻¹ := by
          group
      _ = 1 := by
          rw [← map_mul, ← Subgroup.coe_mul, hg2, Subgroup.coe_one, map_one, mul_one,
            mul_inv_cancel]
  have h1 : A * glAut τ (g : GL (Fin (2 + k)) K) * A⁻¹ = (g : GL (Fin (2 + k)) K) :=
    congrArg Subtype.val (eq_of_uProj_eq_of_mul_self (by omega) hαg.symm hsq hg2)
  have h2 : A * glAut τ (g : GL (Fin (2 + k)) K) = (g : GL (Fin (2 + k)) K) * A :=
    calc A * glAut τ (g : GL (Fin (2 + k)) K) = A * glAut τ (g : GL (Fin (2 + k)) K) * A⁻¹ * A :=
          by group
      _ = (g : GL (Fin (2 + k)) K) * A := by rw [h1]
  have h3 := congrArg Units.val h2
  simpa only [Units.val_mul, coe_glAut] using h3

theorem exists_blk_of_fix_uBarW {ζ : K} (hζ : ζ ^ 2 ^ f * ζ = 1) (hζ1 : ζ ≠ 1)
    (hW : ∀ w ∈ uBarW K k f, α w = w) :
    ∃ (A₁ : Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin k) (Fin k) K), A.val = blk A₁ D := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  obtain ⟨J, hJ⟩ := exists_swapM_mem (K := K) f
  obtain ⟨J', hJ'⟩ := exists_twJ_mem hζ
  have hinv : ∀ X : StatedSU 2 (2 ^ f) K, X * X = 1 → uW K k f X * uW K k f X = 1 :=
    fun X hX => by rw [← map_mul, hX, map_one]
  have e1 := mul_eq_of_fix hα (hinv J (mul_self_eq_one_of_val hJ swapM_mul_swapM))
    (hW _ ⟨J, rfl⟩)
  have e2 := mul_eq_of_fix hα (hinv J' (mul_self_eq_one_of_val hJ' (twJ_mul_twJ hζ0)))
    (hW _ ⟨J', rfl⟩)
  rw [coe_uW, blk_map_one_right, hJ, map_swapM_of] at e1
  rw [coe_uW, blk_map_one_right, hJ', map_twJ_of] at e2
  exact eq_blk_of_mul_eq e1 e2 (det_swapM_sub_twJ hζ1)
    (det_swapM_sub_twJ fun h1 => hζ1 (τ.injective (h1.trans (map_one τ).symm)))

theorem fix_bar_of_fix_uBarW (h : UnitaryFieldData 2 f K) {A₁ : Matrix (Fin 2) (Fin 2) K}
    {D : Matrix (Fin k) (Fin k) K} (hA : A.val = blk A₁ D) (hW : ∀ w ∈ uBarW K k f, α w = w) :
    ∀ c, h.bar c = c → τ c = c := by
  obtain ⟨-, -, hA₁', -, -⟩ := inv_val_of_blk hA
  have key : ∀ c, h.bar c = c → A₁ * (1 + τ c • onesM) = (1 + c • onesM) * A₁ := by
    intro c hc
    obtain ⟨X, hX⟩ := exists_statedSU_eq_of_bar h (det_one_add_smul_onesM c) (by
      rw [map_one_add_smul_onesM, hc, transpose_one_add_smul_onesM, one_add_smul_onesM_mul_self])
    have e := mul_eq_of_fix hα
      (show uW K k f X * uW K k f X = 1 by
        rw [← map_mul, mul_self_eq_one_of_val hX (one_add_smul_onesM_mul_self c), map_one])
      (hW _ ⟨X, rfl⟩)
    rw [coe_uW, blk_map_one_right, hX, hA, blk_mul, blk_mul, map_one_add_smul_onesM] at e
    exact (blk_injective e).1
  have h1 : A₁ * onesM = onesM * A₁ := by
    have := key 1 (map_one h.bar)
    rw [map_one, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at this
    exact add_left_cancel this
  have hne : A₁ * onesM ≠ 0 := by
    intro h0
    apply onesM_ne_zero (K := K)
    rw [← Matrix.one_mul onesM, ← hA₁', Matrix.mul_assoc, h0, Matrix.mul_zero]
  intro c hc
  have h2 := key c hc
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, ← h1] at h2
  have h3 : (τ c - c) • (A₁ * onesM) = 0 := by
    rw [sub_smul, add_left_cancel h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hne)

theorem eq_refl_or_bar_of_fix_uBarW [Finite K] (h : UnitaryFieldData 2 f K)
    {A₁ : Matrix (Fin 2) (Fin 2) K} {D : Matrix (Fin k) (Fin k) K} (hA : A.val = blk A₁ D)
    (hW : ∀ w ∈ uBarW K k f, α w = w) : τ = RingEquiv.refl K ∨ ∀ c, τ c = h.bar c :=
  UnitaryHigher.ringEquiv_eq_refl_or_bar_of_fixes h fun a ha =>
    fix_bar_of_fix_uBarW hα h hA hW a (h.mem_fixedField.mp ha)

theorem mul_eq_of_fix_uBarW {A₁ : Matrix (Fin 2) (Fin 2) K} {D : Matrix (Fin k) (Fin k) K}
    (hA : A.val = blk A₁ D) (hW : ∀ w ∈ uBarW K k f, α w = w) {X : StatedSU 2 (2 ^ f) K}
    (hX : X * X = 1) :
    A₁ * (X : GL (Fin 2) K).val.map τ = (X : GL (Fin 2) K).val * A₁ := by
  have e := mul_eq_of_fix hα (show uW K k f X * uW K k f X = 1 by rw [← map_mul, hX, map_one])
    (hW _ ⟨X, rfl⟩)
  rw [coe_uW, blk_map_one_right, hA, blk_mul, blk_mul] at e
  exact (blk_injective e).1

omit [CharP K 2] in
theorem mul_eq_of_fix_uL {A₁ : Matrix (Fin 2) (Fin 2) K} {D : Matrix (Fin k) (Fin k) K}
    (hA : A.val = blk A₁ D) {S : StatedSU k (2 ^ f) K}
    (hfix : α (uProj K (2 + k) f (uL K k f S)) = uProj K (2 + k) f (uL K k f S)) :
    (S : GL (Fin k) K).val * D = D * (S : GL (Fin k) K).val.map τ := by
  obtain ⟨c, hc⟩ := exists_scalar_of_fix hα hfix
  rw [coe_uL, blk_map_one_left, hA, blk_mul, blk_mul, blk_smul] at hc
  obtain ⟨h1, h2⟩ := blk_injective hc
  rw [Matrix.one_mul, Matrix.mul_one] at h1
  have hA₁ := (det_ne_zero_of_blk hA).1
  have hc1 : (c : K) = 1 := by
    by_contra hne
    have h3 : (1 - (c : K)) • A₁ = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact hne (sub_eq_zero.mp h4).symm
    · rw [h4, det_zero] at hA₁
      exact hA₁ rfl
  rwa [hc1, one_smul] at h2

omit [CharP K 2] in
theorem mul_eq_of_fix_uBarL {A₁ : Matrix (Fin 2) (Fin 2) K} {D : Matrix (Fin k) (Fin k) K}
    (hA : A.val = blk A₁ D) (hL : ∀ l ∈ uBarL K k f, α l = l) (S : StatedSU k (2 ^ f) K) :
    (S : GL (Fin k) K).val * D = D * (S : GL (Fin k) K).val.map τ :=
  mul_eq_of_fix_uL hα hA (hL _ ⟨S, rfl⟩)

end Fix

end CFSG.ComponentClassification.RankTwoClassical
