module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIYComponent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityUnitary
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofCore

public section

namespace CFSG.ComponentClassification.RankTwoHypIIL3

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {K : Type} [Field K]

section Swap

variable (K) in
@[expose] def swapMat : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem swapMat_mul_self : swapMat K * swapMat K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

variable (K) in
@[expose] def swapGL : GL (Fin 3) K :=
  ⟨swapMat K, swapMat K, swapMat_mul_self, swapMat_mul_self⟩

theorem coe_swapGL : (swapGL K : Matrix (Fin 3) (Fin 3) K) = swapMat K := rfl

theorem swapGL_mul_self : swapGL K * swapGL K = 1 :=
  Units.ext swapMat_mul_self

theorem swapMat_transpose : (swapMat K)ᵀ = swapMat K := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem swapMat_map (φ : K →+* K) : (swapMat K).map φ = swapMat K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem det_swapMat [CharP K 2] : (swapMat K).det = 1 := by
  simp [swapMat, Matrix.det_fin_three, CharTwo.neg_eq]

theorem conjAut_swapGL_ne_one [Finite K] : conjAut 3 K (swapGL K) ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff le_rfl _).mp h
  have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) hc
  simp [coe_swapGL, swapMat, GeneralLinearGroup.coe_scalar] at this

theorem conjAut_swapGL_sq : conjAut 3 K (swapGL K) ^ 2 = 1 := by
  rw [sq, ← map_mul, swapGL_mul_self, map_one]

end Swap

theorem isSimpleGroup_projectiveSL_three (k : Type*) [Field k] :
    IsSimpleGroup (projectiveSL 3 k) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := k) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k).symm.isSimpleGroup

theorem center_projectiveSL_three_eq_bot (k : Type*) [Field k] :
    center (projectiveSL 3 k) = ⊥ := by
  have := isSimpleGroup_projectiveSL_three k
  have hperf : Group.IsPerfect (projectiveSL 3 k) := by
    have := CFSG.LinearGroups.linear_projective_perfect (K := k) (n := 3) (by norm_num)
      (Or.inl le_rfl)
    exact Group.IsPerfect.ofSurjective
      (f := (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k).toMonoidHom)
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k).surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (projectiveSL 3 k)) with h | h
  · exact h
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top (projectiveSL 3 k)).2 h
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_ne_bot h1

theorem isSimpleGroup_SL2 [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (SpecialLinearGroup (Fin 2) K) :=
  CFSG.RankThree.PartTwo.Sec21.Item228Census4Proof.isSimpleGroup_SL_two_of_charTwo h4

theorem rigidInvolution_fieldAut [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hX : fieldAut 3 K σ ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (h2 : fieldAut 3 K σ ^ 2 = 1) :
    RigidInvolution (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
      (fieldAut 3 K σ) := by
  obtain ⟨-, ⟨e, -⟩, hinn, -, hcent, hnorm, hC⟩ :=
    linear_quadratic_field_full_centralizer_rigidity (n := 3) σ le_rfl
  have := isSimpleGroup_projectiveSL_three (fixedField K σ)
  refine RigidInvolution.of_isSimpleGroup_of_le_zpowers hX h2 hinn hcent
    ((normal_subgroupOf_iff_le_normalizer hcent).mp hnorm) e.symm.isSimpleGroup ?_ ?_
  · refine even_card_of_mem ?_ conjAut_swapGL_ne_one conjAut_swapGL_sq
    rw [range_subfieldConj]
    refine ⟨swapGL K, ⟨?_, ?_⟩, rfl⟩
    · exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, coe_swapGL, det_swapMat]; rfl)
    · exact Units.ext (swapMat_map _)
  · rw [hC]
    exact inf_le_right

theorem nonempty_matrixIsometryGroup_one_mulEquiv_SL2 [CharP K 2] :
    Nonempty (FourGroupEvenCanonical.matrixIsometryGroup
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≃* SpecialLinearGroup (Fin 2) K) := by
  have hr : 3 = 2 * 1 + 1 := rfl
  obtain ⟨e⟩ := CatalogueBAlternatingIsometry.exists_planeIsometryEquivSL _
    (OutcomeLocal.dotForm_restrict_isAlt (k := K) (n := 3))
    (OutcomeLocal.dotForm_restrict_nondegenerate hr)
    (by rw [OutcomeLocal.finrank_dotForm_ker hr])
  exact ⟨(OutcomeLocal.oneRestrictEquiv hr).trans e⟩

theorem rigidInvolution_dualAut [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hX : dualAut 3 K ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    RigidInvolution (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
      (dualAut 3 K) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  obtain ⟨hinj, hinn, hβ2, -, hcent, hnorm, hrest⟩ :=
    even_linear_canonical_graph_symplectic_centralizers (n := 3) (by omega) hK le_rfl 1
      (Or.inl rfl)
  obtain ⟨hC, -⟩ := hrest (Or.inr ⟨rfl, by decide⟩)
  have hβ : conjAut 3 K 1 * dualAut 3 K = dualAut 3 K := by rw [map_one, one_mul]
  rw [hβ] at hβ2 hcent hnorm hC
  set O := FourGroupEvenCanonical.matrixIsometryGroup
    ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hO
  have hNO : ((conjAut 3 K).comp O.subtype).range = O.map (conjAut 3 K) := by
    rw [MonoidHom.range_comp, range_subtype]
  obtain ⟨eSL⟩ := nonempty_matrixIsometryGroup_one_mulEquiv_SL2 (K := K)
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := isSimpleGroup_SL2 h4
  have hsimple : IsSimpleGroup (O.map (conjAut 3 K)) :=
    ((MulEquiv.subgroupCongr hNO).symm.trans
      ((MonoidHom.ofInjective hinj).symm.trans eSL)).isSimpleGroup
  refine RigidInvolution.of_isSimpleGroup_of_le_zpowers hX hβ2 hinn hcent
    ((normal_subgroupOf_iff_le_normalizer hcent).mp hnorm) hsimple ?_ hC.le
  refine even_card_of_mem (mem_map_of_mem _ ?_) conjAut_swapGL_ne_one conjAut_swapGL_sq
  rw [hO, FourGroupEvenCanonical.mem_matrixIsometryGroup, Units.val_one, Matrix.mul_one,
    coe_swapGL, swapMat_transpose, swapMat_mul_self]

theorem rigidInvolution_graphField {e : ℕ} (h : UnitaryFieldData 2 e K) (he : 2 ≤ e)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (hX : fieldAut 3 K σ * dualAut 3 K ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (h2 : (fieldAut 3 K σ * dualAut 3 K) ^ 2 = 1) :
    RigidInvolution (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
      (fieldAut 3 K σ * dualAut 3 K) := by
  have := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ι, -⟩, hinn, -, hcent, hnorm, hC⟩ :=
    linear_graph_field_full_centralizer_rigidity h (n := 3) le_rfl σ hσ
  have hq : ((3 : ℕ), 2 ^ e) ≠ (3, 2) := by
    intro hq
    have h2e : 2 ^ e = 2 ^ 1 := by simpa using congrArg Prod.snd hq
    have := Nat.pow_right_injective le_rfl h2e
    omega
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 e
    (by rw [h.card, ← pow_mul, mul_comm]) 3 le_rfl hq
  have hsimple := (ι.symm.trans
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by norm_num))).isSimpleGroup
  refine RigidInvolution.of_isSimpleGroup_of_le_zpowers hX h2 hinn hcent
    ((normal_subgroupOf_iff_le_normalizer hcent).mp hnorm) hsimple ?_ ?_
  · refine even_card_of_mem (mem_map_of_mem _ ?_) conjAut_swapGL_ne_one conjAut_swapGL_sq
    rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h, coe_swapGL, det_swapMat,
      swapMat_map, swapMat_transpose, swapMat_mul_self]
    exact ⟨rfl, rfl⟩
  · rw [hC]
    exact inf_le_right

end CFSG.ComponentClassification.RankTwoHypIIL3
