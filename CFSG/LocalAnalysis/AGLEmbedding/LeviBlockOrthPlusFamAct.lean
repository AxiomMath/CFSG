module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFam
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusCuts
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise MatrixGroups

variable {K : Type} [Field K]

theorem swapPair_one_symm_apply (x : Fin 2 ⊕ Fin 2 → K) :
    (swapPair K (1 : Fin 2)).symm x (Sum.inl 0) = x (Sum.inl 0) ∧
      (swapPair K (1 : Fin 2)).symm x (Sum.inl 1) = x (Sum.inr 1) ∧
      (swapPair K (1 : Fin 2)).symm x (Sum.inr 0) = x (Sum.inr 0) ∧
      (swapPair K (1 : Fin 2)).symm x (Sum.inr 1) = x (Sum.inl 1) := by
  have h : (swapPair K (1 : Fin 2)).symm = swapPair K 1 :=
    inv_eq_of_mul_eq_one_right (swapPair_mul_self 1)
  rw [h]
  simp only [swapPair_apply]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> congr 1

theorem swapPair_smul_plusFamTwo (p : Fin 2 → K) :
    swapPair K (1 : Fin 2) • plusFamTwo p = plusFamOne p := by
  ext x
  change x ∈ (plusFamTwo p).map (swapPair K (1 : Fin 2) : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] _) ↔ _
  rw [Submodule.mem_map_equiv, mem_plusFamTwo, mem_plusFamOne]
  obtain ⟨h0, h1, h2, h3⟩ := swapPair_one_symm_apply x
  rw [h0, h1, h2, h3]

theorem swapPair_smul_plusFamOne (p : Fin 2 → K) :
    swapPair K (1 : Fin 2) • plusFamOne p = plusFamTwo p := by
  rw [← swapPair_smul_plusFamTwo, smul_smul, swapPair_mul_self, one_smul]

@[expose] noncomputable def plusXBlock :
    ↥(MulAction.stabilizer ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (flag 2 K 2)) →*
      GL (Fin 2) K :=
  plusBlockHom _ Sum.inl_injective
    (fun x => by
      rcases x with i | i
      · rw [plusPos_inl]
        exact ⟨fun _ => ⟨Nat.zero_le _, i.isLt⟩, fun _ => ⟨i, rfl⟩⟩
      · rw [plusPos_inr]
        refine ⟨fun ⟨_, h⟩ => absurd h Sum.inl_ne_inr, fun h => ?_⟩
        have := i.isLt
        omega)
    (fun g _ => plusCut_zero g) (fun _ hg => plusCut_of_smul_flag le_rfl hg)

theorem coe_plusXBlock
    (g : ↥(MulAction.stabilizer ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (flag 2 K 2)))
    (i j : Fin 2) :
    ((plusXBlock g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      autMat (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (Sum.inl i) (Sum.inl j) :=
  rfl

theorem stab_apply_elim
    (g : ↥(MulAction.stabilizer ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (flag 2 K 2)))
    (p : Fin 2 → K) :
    (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (Sum.elim p 0) =
      Sum.elim (((plusXBlock g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ p) 0 := by
  have hcut := plusCut_of_smul_flag (le_refl 2) (MulAction.mem_stabilizer_iff.1 g.2)
  funext c
  rw [apply_eq_autMat_mulVec, mulVec, dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    Sum.elim_inl]
  rcases c with i | i
  · simp only [Sum.elim_inl, mulVec, dotProduct, coe_plusXBlock]
  · simp only [Sum.elim_inr, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hcut _ _ (by rw [plusPos_inl]; exact j.isLt) (by rw [plusPos_inr]; have := i.isLt; omega),
      zero_mul]

variable [CharP K 2]

theorem smul_plusFamTwo_le_of_stab
    (g : ↥(MulAction.stabilizer ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (flag 2 K 2)))
    (hgO : (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)) {p : Fin 2 → K} (hp : p ≠ 0) :
    (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) • plusFamTwo p ≤
      plusFamTwo (((plusXBlock g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ p) := by
  have hgX : (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) • flag 2 K 2 = flag 2 K 2 :=
    MulAction.mem_stabilizer_iff.1 g.2
  refine plusFamTwo_le_of_isotropic ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    change quadPlus 2 K ((g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) x) = 0
    rw [map_of_mem hgO]
    exact plusFamTwo_isotropic hp hx
  · rw [← stab_apply_elim]
    exact ⟨_, ⟨by simp [mul_comm], by simp⟩, rfl⟩
  · intro hle
    set w : Fin 2 ⊕ Fin 2 → K := Sum.elim 0 ![p 1, p 0] with hw
    have hwP : w ∈ plusFamTwo p := ⟨by simp [hw], by simp [hw, mul_comm]⟩
    have hgw := hle ⟨w, hwP, rfl⟩
    rw [← flag_two_eq_plusFamOne] at hgw
    have hgw' : (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) w ∈
        (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) • flag 2 K 2 := by
      rw [hgX]
      exact hgw
    obtain ⟨w', hw', hww'⟩ := hgw'
    have : w' = w := (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)).injective hww'
    rw [this, flag_two_eq_plusFamOne, SetLike.mem_coe, mem_plusFamOne_one_zero] at hw'
    apply hp
    funext i
    fin_cases i
    · simpa [hw] using hw'.2
    · simpa [hw] using hw'.1

theorem smul_plusFamTwo_of_stab
    (g : ↥(MulAction.stabilizer ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) (flag 2 K 2)))
    (hgO : (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)) {p : Fin 2 → K} (hp : p ≠ 0) :
    (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) • plusFamTwo p =
      plusFamTwo (((plusXBlock g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ p) := by
  set M := ((plusXBlock g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
  have hMinv : ((plusXBlock g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M = 1 := by
    rw [hM, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hMp : M *ᵥ p ≠ 0 := fun h => hp (by
    rw [← one_mulVec p, ← hMinv, ← mulVec_mulVec, h, mulVec_zero])
  refine le_antisymm (smul_plusFamTwo_le_of_stab g hgO hp) ?_
  have hinvO : ((g⁻¹ : ↥(MulAction.stabilizer _ (flag 2 K 2))) :
      (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K) := inv_mem hgO
  have h := smul_plusFamTwo_le_of_stab g⁻¹ hinvO hMp
  rw [mulVec_mulVec, hMinv, one_mulVec] at h
  intro x hx
  refine ⟨(g⁻¹ : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) x, ?_, ?_⟩
  · exact h ⟨x, hx, rfl⟩
  · change (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K))
      ((g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K))⁻¹ x) = x
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl

variable (K) in
@[expose] noncomputable def plusIotaTwo :
    SL(2, K) →* ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
  (levi 2 K).comp SpecialLinearGroup.toGL

omit [CharP K 2] in
theorem plusIotaTwo_apply_inl (A : SL(2, K)) (x : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    plusIotaTwo K A x (Sum.inl i) = ∑ j, A i j * x (Sum.inl j) := by
  rw [apply_eq_autMat_mulVec, plusIotaTwo, MonoidHom.comp_apply, autMat_apply, toMatrix'_levi_eq]
  simp [mulVec, dotProduct, Fintype.sum_sum_type]

omit [CharP K 2] in
theorem plusIotaTwo_apply_inr (A : SL(2, K)) (x : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    plusIotaTwo K A x (Sum.inr i) = ∑ j, (A⁻¹ : SL(2, K)) j i * x (Sum.inr j) := by
  have hinv : (((SpecialLinearGroup.toGL A)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← map_inv]
    rfl
  rw [apply_eq_autMat_mulVec, plusIotaTwo, MonoidHom.comp_apply, autMat_apply, toMatrix'_levi_eq,
    hinv]
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, transpose_apply]

omit [CharP K 2] in
theorem plusIotaTwo_mem_orthogonalGroup (A : SL(2, K)) :
    plusIotaTwo K A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K) :=
  levi_mem_orthogonalGroup _

omit [CharP K 2] in
theorem plusIotaTwo_mem_stabilizer (A : SL(2, K)) :
    plusIotaTwo K A ∈ MulAction.stabilizer ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K))
      (flag 2 K 2) :=
  MulAction.mem_stabilizer_iff.2 (mem_maxStab.1 (levi_mem_maxStab _)).2

omit [CharP K 2] in
theorem plusXBlock_plusIotaTwo (A : SL(2, K)) :
    ((plusXBlock ⟨plusIotaTwo K A, plusIotaTwo_mem_stabilizer A⟩ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = A := by
  ext i j
  rw [coe_plusXBlock]
  change autMat (plusIotaTwo K A) _ _ = _
  rw [plusIotaTwo, MonoidHom.comp_apply, autMat_apply, toMatrix'_levi_eq, fromBlocks_apply₁₁]
  rfl

theorem plusIotaTwo_smul_plusFamTwo (A : SL(2, K)) {p : Fin 2 → K} (hp : p ≠ 0) :
    plusIotaTwo K A • plusFamTwo p = plusFamTwo ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ p) := by
  have h := smul_plusFamTwo_of_stab ⟨plusIotaTwo K A, plusIotaTwo_mem_stabilizer A⟩
    (plusIotaTwo_mem_orthogonalGroup A) hp
  rwa [plusXBlock_plusIotaTwo] at h

theorem plusIotaTwo_smul_plusFamOne_le (A : SL(2, K)) (p : Fin 2 → K) :
    plusIotaTwo K A • plusFamOne p ≤ plusFamOne p := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨h1, h3⟩ := mem_plusFamOne.1 hx
  change plusIotaTwo K A x ∈ plusFamOne p
  rw [mem_plusFamOne, plusIotaTwo_apply_inl, plusIotaTwo_apply_inl, plusIotaTwo_apply_inr,
    plusIotaTwo_apply_inr, Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  constructor
  · linear_combination (A 0 0) * h1 + (A 0 1) * h3 + A 0 1 * x (Sum.inr 0) * p 0 * h2
  · linear_combination (A 1 0) * h1 + (A 1 1) * h3 + A 1 0 * x (Sum.inr 1) * p 0 * h2

theorem plusIotaTwo_smul_plusFamOne (A : SL(2, K)) (p : Fin 2 → K) :
    plusIotaTwo K A • plusFamOne p = plusFamOne p := by
  refine le_antisymm (plusIotaTwo_smul_plusFamOne_le A p) ?_
  have h := plusIotaTwo_smul_plusFamOne_le A⁻¹ p
  intro x hx
  refine ⟨plusIotaTwo K A⁻¹ x, h ⟨x, hx, rfl⟩, ?_⟩
  change plusIotaTwo K A (plusIotaTwo K A⁻¹ x) = x
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

end CFSG.AGLEmbedding.LeviBlock
