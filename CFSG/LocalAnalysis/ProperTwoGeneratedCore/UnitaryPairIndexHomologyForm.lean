module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.UnitaryForm
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Homology

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.BenderSuzuki.MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

@[expose] def hermForm (hK : UnitaryFieldData p f K) (J : HermitianForm n K) :
    (Fin n → K) →ₛₗ[hK.bar] (Fin n → K) →ₗ[K] K :=
  Matrix.toLinearMapₛₗ₂' K hK.bar (RingHom.id K) J.form

variable (hK : UnitaryFieldData p f K) {J : HermitianForm n K}

theorem hermForm_apply (x y : Fin n → K) :
    hermForm hK J x y = (hK.bar ∘ x) ⬝ᵥ (J.form *ᵥ y) := by
  rw [hermForm, Matrix.toLinearMapₛₗ₂'_apply]
  simp only [RingHom.id_apply, smul_eq_mul, dotProduct, mulVec, Function.comp_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {hK}

theorem conjTranspose_eq (hJ : ∀ c, J.conj c = hK.bar c) (A : Matrix (Fin n) (Fin n) K) :
    J.conjTranspose A = (A.map hK.bar)ᵀ := by
  ext i j
  simp [HermitianForm.conjTranspose, hJ]

theorem bar_comp_single (i : Fin n) : hK.bar ∘ (Pi.single i 1 : Fin n → K) = Pi.single i 1 := by
  ext a
  by_cases ha : a = i
  · subst ha
    simp
  · simp [ha]

theorem hermForm_mulVec (hJ : ∀ c, J.conj c = hK.bar c) (A : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) :
    hermForm hK J (A *ᵥ x) (A *ᵥ y) =
      (hK.bar ∘ x) ⬝ᵥ ((J.conjTranspose A * J.form * A) *ᵥ y) := by
  rw [hermForm_apply, conjTranspose_eq hJ]
  have hσ : hK.bar ∘ (A *ᵥ x) = (A.map hK.bar) *ᵥ (hK.bar ∘ x) := by
    ext a
    rw [Function.comp_apply, RingHom.map_mulVec]
  rw [hσ, CFSG.UnitaryInvolutionIndex.mulVec_dotProduct_eq, mulVec_mulVec, mulVec_mulVec]

theorem dotProduct_single_mulVec_single (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (hK.bar ∘ (Pi.single i 1 : Fin n → K)) ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  rw [bar_comp_single, single_one_dotProduct, mulVec_single_one]
  rfl

theorem hermForm_mulVec_single (hJ : ∀ c, J.conj c = hK.bar c) (A : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) :
    hermForm hK J (A *ᵥ Pi.single i 1) (A *ᵥ Pi.single j 1) =
      (J.conjTranspose A * J.form * A) i j := by
  rw [hermForm_mulVec hJ, dotProduct_single_mulVec_single]

theorem hermForm_isSymm (hJ : ∀ c, J.conj c = hK.bar c) : (hermForm hK J).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [hermForm, Matrix.toLinearMapₛₗ₂'_apply, Matrix.toLinearMapₛₗ₂'_apply, map_sum,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_eq_mul, RingHom.id_apply, map_mul, hK.bar_bar]
  rw [← hJ (J.form j i), J.form_hermitian i j]
  ring

theorem hermForm_separatingLeft : (hermForm hK J).SeparatingLeft := by
  intro x hx
  have hvec : (hK.bar ∘ x) ᵥ* J.form = 0 := by
    ext j
    have h := hx (Pi.single j 1)
    rw [hermForm_apply, dotProduct_mulVec, dotProduct_single_one] at h
    exact h
  by_contra hx0
  have hσx : hK.bar ∘ x ≠ 0 := by
    intro h0
    apply hx0
    ext i
    have h := congrFun h0 i
    simpa using h
  exact J.form_nondegenerate (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hσx, hvec⟩)

theorem toLin_apply' (g : GL (Fin n) K) (x : Fin n → K) :
    ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      (Fin n → K) →ₗ[K] Fin n → K) x = (g : Matrix (Fin n) (Fin n) K) *ᵥ x :=
  rfl

theorem forall_hermForm_mulVec_iff (hJ : ∀ c, J.conj c = hK.bar c)
    (A : Matrix (Fin n) (Fin n) K) :
    (∀ x y, hermForm hK J (A *ᵥ x) (A *ᵥ y) = hermForm hK J x y) ↔
      J.conjTranspose A * J.form * A = J.form := by
  constructor
  · intro h
    ext i j
    have h1 := h (Pi.single i 1) (Pi.single j 1)
    rw [hermForm_mulVec_single hJ, ← Matrix.one_mulVec (Pi.single i 1),
      ← Matrix.one_mulVec (Pi.single j 1), hermForm_mulVec_single hJ] at h1
    simpa [conjTranspose_eq hJ] using h1
  · intro h x y
    rw [hermForm_mulVec hJ, h, hermForm_apply]

theorem toLin_mem_sesqSpecialUnitaryGroup_iff (hJ : ∀ c, J.conj c = hK.bar c)
    (g : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqSpecialUnitaryGroup (hermForm hK J) ↔
      g ∈ J.specialSubgroup := by
  rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, HermitianForm.mem_specialSubgroup_iff]
  simp only [toLin_apply']
  rw [forall_hermForm_mulVec_iff hJ]
  have hdet : LinearMap.det ((Matrix.GeneralLinearGroup.toLin g :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : (Fin n → K) →ₗ[K] Fin n → K) =
      (g : Matrix (Fin n) (Fin n) K).det := by
    rw [Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  rw [hdet, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

variable (hK) in
theorem map_toLin_specialSubgroup (hJ : ∀ c, J.conj c = hK.bar c) :
    J.specialSubgroup.map (Matrix.GeneralLinearGroup.toLin :
      GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom =
      sesqSpecialUnitaryGroup (hermForm hK J) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff hJ A).2 hA
  · intro hg
    obtain ⟨A, rfl⟩ := (Matrix.GeneralLinearGroup.toLin :
      GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)).surjective g
    exact ⟨A, (toLin_mem_sesqSpecialUnitaryGroup_iff hJ A).1 hg, rfl⟩

variable (hK) in
@[expose] def specialSubgroupEquiv (hJ : ∀ c, J.conj c = hK.bar c) :
    J.specialSubgroup ≃* sesqSpecialUnitaryGroup (hermForm hK J) :=
  ((Matrix.GeneralLinearGroup.toLin :
      GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)).subgroupMap
    J.specialSubgroup).trans (MulEquiv.subgroupCongr (map_toLin_specialSubgroup hK hJ))

theorem coe_specialSubgroupEquiv (hJ : ∀ c, J.conj c = hK.bar c) (g : J.specialSubgroup) :
    (specialSubgroupEquiv hK hJ g : LinearMap.GeneralLinearGroup K (Fin n → K)) =
      Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) :=
  rfl

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Homology
