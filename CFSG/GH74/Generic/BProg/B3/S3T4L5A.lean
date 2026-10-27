module

public import CFSG.LocalAnalysis.ComponentInitial.OddProjectivePairExclusion

public section

namespace CFSG.GH74.Generic.BProg.B3

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspace
  CFSG.LocalAnalysis.ComponentInitial.OddProjectivePair
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution

namespace S3T4

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_fin_ne {r : ℕ} (hr : 2 ≤ r) (i : Fin r) : ∃ j : Fin r, j ≠ i := by
  by_cases hi : (i : ℕ) = 0
  · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hi; simp at hi⟩
  · exact ⟨⟨0, by omega⟩, fun h => hi (by rw [← h])⟩

theorem le_of_forall_sub_mem (htwo : (2 : K) ≠ 0) {A W A' : Submodule K (Fin n → K)}
    (hAW : IsCompl A W) (hA2 : 2 ≤ Module.finrank K A)
    (h : ∀ g ∈ summandSpecialLinear A W, ∀ x : Fin n → K,
      (g : Matrix (Fin n) (Fin n) K) *ᵥ x - x ∈ A') : A ≤ A' := by
  set b := Module.finBasis K A
  have hbi : ∀ i, (b i : Fin n → K) ∈ A' := by
    intro i
    obtain ⟨j, hj⟩ := exists_fin_ne hA2 i
    have hg := summandDiagonal_mem hAW b (signs i j) (signs_mul_self i j) (prod_signs i j)
    have h1 := h _ hg (b i)
    rw [summandDiagonal_mulVec_basis, signs_left hj.symm] at h1
    have h2 : (-1 : K) • (b i : Fin n → K) - b i = (-2 : K) • (b i : Fin n → K) := by
      rw [neg_smul, one_smul, show (-2 : K) = -(1 + 1) by norm_num, neg_smul, add_smul,
        one_smul]
      abel
    rw [h2] at h1
    have h3 := A'.smul_mem (-2 : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 htwo), one_smul] at h3
  intro a ha
  have h1 : (⟨a, ha⟩ : A) = ∑ i, b.repr ⟨a, ha⟩ i • b i := (b.sum_repr _).symm
  have h2 := congrArg Subtype.val h1
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  rw [h2]
  exact A'.sum_mem fun i _ => A'.smul_mem _ (hbi i)

theorem eq_zero_of_forall_fix (htwo : (2 : K) ≠ 0) {A W : Submodule K (Fin n → K)}
    (hAW : IsCompl A W) (hA2 : 2 ≤ Module.finrank K A) {a : Fin n → K} (ha : a ∈ A)
    (h : ∀ g ∈ summandSpecialLinear A W, (g : Matrix (Fin n) (Fin n) K) *ᵥ a = a) : a = 0 := by
  set b := Module.finBasis K A
  have hc : ∀ i, b.repr ⟨a, ha⟩ i = 0 := by
    intro i
    obtain ⟨j, hj⟩ := exists_fin_ne hA2 i
    have hg := summandDiagonal_mem hAW b (signs i j) (signs_mul_self i j) (prod_signs i j)
    have h1 := h _ hg
    rw [summandDiagonal_mulVec, summandDiagonalMap_left hAW b _ ⟨a, ha⟩] at h1
    have h2 : Matrix.toLin b b (Matrix.diagonal (signs i j)) ⟨a, ha⟩ = ⟨a, ha⟩ :=
      Subtype.ext h1
    have h3 := congrArg (fun x => b.repr x i) h2
    rw [← LinearMap.toMatrix_mulVec_repr b b, LinearMap.toMatrix_toLin, mulVec_diagonal,
      signs_left hj.symm] at h3
    have h4 : (2 : K) * b.repr ⟨a, ha⟩ i = 0 := by linear_combination -h3
    exact (mul_eq_zero.1 h4).resolve_left htwo
  have h0 : (⟨a, ha⟩ : A) = 0 :=
    b.ext_elem fun i => by rw [hc i, map_zero, Finsupp.zero_apply]
  exact congrArg Subtype.val h0

theorem le_of_summandSL_eq (htwo : (2 : K) ≠ 0) {A₁ W₁ A₂ W₂ : Submodule K (Fin n → K)}
    (h₁ : IsCompl A₁ W₁) (h₂ : IsCompl A₂ W₂) (hA₁ : 2 ≤ Module.finrank K A₁)
    (hA₂ : 2 ≤ Module.finrank K A₂)
    (heq : summandSpecialLinear A₁ W₁ = summandSpecialLinear A₂ W₂) : A₁ ≤ A₂ ∧ W₁ ≤ W₂ := by
  constructor
  · refine le_of_forall_sub_mem htwo h₁ hA₁ fun g hg x => ?_
    rw [heq] at hg
    obtain ⟨hgW, hgA, -⟩ := hg
    obtain ⟨a, ha, w, hw, rfl⟩ :=
      Submodule.mem_sup.1 (h₂.sup_eq_top ▸ Submodule.mem_top : x ∈ A₂ ⊔ W₂)
    rw [mulVec_add, hgW w hw, add_sub_add_right_eq_sub]
    exact A₂.sub_mem (hgA a ha) ha
  · intro x hx
    obtain ⟨a, ha, w, hw, rfl⟩ :=
      Submodule.mem_sup.1 (h₂.sup_eq_top ▸ Submodule.mem_top : x ∈ A₂ ⊔ W₂)
    have ha0 : a = 0 := by
      refine eq_zero_of_forall_fix htwo h₂ hA₂ ha fun g hg => ?_
      have hg' : g ∈ summandSpecialLinear A₁ W₁ := heq ▸ hg
      have h1 := hg'.1 _ hx
      rw [mulVec_add, hg.1 w hw] at h1
      exact add_right_cancel h1
    rw [ha0, zero_add]
    exact hw

theorem mul_eq_scalar_of_summandSL_eq (htwo : (2 : K) ≠ 0) {T₁ T₂ : GL (Fin n) K} {c₁ c₂ : Kˣ}
    (hsq₁ : T₁ ^ 2 = GeneralLinearGroup.scalar (Fin n) (c₁ ^ 2))
    (hsq₂ : T₂ ^ 2 = GeneralLinearGroup.scalar (Fin n) (c₂ ^ 2))
    (hA₁ : 2 ≤ Module.finrank K ((splitMatrixOperator T₁).eigenspace c₁.val))
    (hA₂ : 2 ≤ Module.finrank K ((splitMatrixOperator T₂).eigenspace c₂.val))
    (heq : summandSpecialLinear ((splitMatrixOperator T₁).eigenspace c₁.val)
        ((splitMatrixOperator T₁).eigenspace (-c₁.val)) =
      summandSpecialLinear ((splitMatrixOperator T₂).eigenspace c₂.val)
        ((splitMatrixOperator T₂).eigenspace (-c₂.val))) :
    T₁ * T₂ = GeneralLinearGroup.scalar (Fin n) (c₁ * c₂) := by
  have h₁ := squareScalar_eigenspaces_isCompl (splitMatrixOperator T₁) c₁.val c₁.ne_zero htwo
    (splitMatrixOperator_square T₁ c₁ hsq₁)
  have h₂ := squareScalar_eigenspaces_isCompl (splitMatrixOperator T₂) c₂.val c₂.ne_zero htwo
    (splitMatrixOperator_square T₂ c₂ hsq₂)
  obtain ⟨hA12, hW12⟩ := le_of_summandSL_eq htwo h₁ h₂ hA₁ hA₂ heq
  refine Units.ext (matrix_eq_of_mulVec_eq fun x => ?_)
  obtain ⟨a, ha, w, hw, rfl⟩ :=
    Submodule.mem_sup.1 (h₁.sup_eq_top ▸ Submodule.mem_top : x ∈ _ ⊔ _)
  have ha₁ := Module.End.mem_eigenspace_iff.1 ha
  have ha₂ := Module.End.mem_eigenspace_iff.1 (hA12 ha)
  have hw₁ := Module.End.mem_eigenspace_iff.1 hw
  have hw₂ := Module.End.mem_eigenspace_iff.1 (hW12 hw)
  change (T₁ : Matrix (Fin n) (Fin n) K) *ᵥ a = c₁.val • a at ha₁
  change (T₂ : Matrix (Fin n) (Fin n) K) *ᵥ a = c₂.val • a at ha₂
  change (T₁ : Matrix (Fin n) (Fin n) K) *ᵥ w = (-c₁.val) • w at hw₁
  change (T₂ : Matrix (Fin n) (Fin n) K) *ᵥ w = (-c₂.val) • w at hw₂
  rw [Units.val_mul, ← mulVec_mulVec, mulVec_add, mulVec_add, ha₂, hw₂, mulVec_smul, mulVec_smul,
    ha₁, hw₁, GeneralLinearGroup.coe_scalar, smul_smul, smul_smul, neg_mul_neg]
  have hs : ∀ y : Fin n → K, (scalar (Fin n) ((c₁ * c₂ : Kˣ) : K)) *ᵥ y =
      ((c₁ * c₂ : Kˣ) : K) • y := by
    intro y
    ext i
    simp [scalar_apply, mulVec_diagonal]
  rw [hs, smul_add, Units.val_mul, mul_comm (c₂ : K)]

end S3T4

end CFSG.GH74.Generic.BProg.B3
