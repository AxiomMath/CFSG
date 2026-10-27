module

public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.UnitaryForm
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryInvolutionIndex

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def hermitianSesquilinear (J : HermitianForm n K) :
    (Fin n → K) →ₛₗ[J.conj.toRingHom] (Fin n → K) →ₗ[K] K :=
  Matrix.toLinearMapₛₗ₂' K J.conj.toRingHom (RingHom.id K) J.form

theorem gram_hermitianSesquilinear (J : HermitianForm n K) :
    gram (hermitianSesquilinear J) = J.form := by
  ext i j
  rw [gram, hermitianSesquilinear, Matrix.toLinearMapₛₗ₂'_apply]
  simp [Pi.single_apply]

theorem conjTranspose_eq_transpose_map (J : HermitianForm n K) (A : Matrix (Fin n) (Fin n) K) :
    J.conjTranspose A = (A.map J.conj.toRingHom)ᵀ := rfl

theorem hermitianSesquilinear_nondegenerate (J : HermitianForm n K) :
    (hermitianSesquilinear J).Nondegenerate := by
  set h := hermitianSesquilinear J
  have happ : ∀ v w, h v w = (J.conj.toRingHom ∘ v) ⬝ᵥ (J.form *ᵥ w) := fun v w => by
    rw [apply_eq_dotProduct_gram, gram_hermitianSesquilinear]
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · have hvec : (J.conj.toRingHom ∘ v) ᵥ* J.form = 0 := by
      ext j
      have := hv (Pi.single j 1)
      rw [happ, dotProduct_mulVec] at this
      simpa [dotProduct, Pi.single_apply] using this
    by_contra hv0
    have hσv : J.conj.toRingHom ∘ v ≠ 0 := by
      intro h0
      apply hv0
      ext i
      have := congrFun h0 i
      simpa using this
    exact J.form_nondegenerate (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hσv, hvec⟩)
  · have hvec : J.form *ᵥ w = 0 := by
      ext i
      have := hw (fun k => J.conj.symm ((Pi.single i (1 : K) : Fin n → K) k))
      rw [happ] at this
      have hσ : (J.conj.toRingHom ∘ fun k => J.conj.symm ((Pi.single i (1 : K) : Fin n → K) k)) =
          (Pi.single i 1 : Fin n → K) := by
        ext k
        simp
      rw [hσ] at this
      simpa [dotProduct, Pi.single_apply] using this
    by_contra hw0
    exact J.form_nondegenerate (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, hvec⟩)

theorem mem_unitaryGroup_hermitianSesquilinear_iff (J : HermitianForm n K)
    (g : GL (Fin n) K) :
    g ∈ unitaryGroup (hermitianSesquilinear J) ↔ g ∈ J.unitarySubgroup := by
  rw [HermitianForm.mem_unitarySubgroup_iff, conjTranspose_eq_transpose_map]
  constructor
  · intro hg
    have := transpose_map_mul_gram_mul hg
    rwa [gram_hermitianSesquilinear] at this
  · intro hg v w
    rw [apply_eq_dotProduct_gram, apply_eq_dotProduct_gram, gram_hermitianSesquilinear]
    have hσg : J.conj.toRingHom ∘ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        ((g : Matrix (Fin n) (Fin n) K).map J.conj.toRingHom) *ᵥ (J.conj.toRingHom ∘ v) := by
      ext a
      rw [Function.comp_apply, RingHom.map_mulVec]
    rw [hσg, mulVec_dotProduct_eq, mulVec_mulVec, mulVec_mulVec, hg]

theorem toGL_mem_specialSubgroup (J : HermitianForm n K)
    (g : specialUnitaryGroup (hermitianSesquilinear J)) :
    Matrix.SpecialLinearGroup.toGL (g : SpecialLinearGroup (Fin n) K) ∈ J.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff, ← HermitianForm.mem_unitarySubgroup_iff,
    ← mem_unitaryGroup_hermitianSesquilinear_iff]
  refine ⟨g.2, ?_⟩
  ext
  simp

@[expose] def toProjectiveSpecialUnitary (J : HermitianForm n K) :
    specialUnitaryGroup (hermitianSesquilinear J) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  ((ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL).comp
    (specialUnitaryGroup (hermitianSesquilinear J)).subtype).codRestrict _
    fun g => Subgroup.mem_map_of_mem _ (toGL_mem_specialSubgroup J g)

theorem toProjectiveSpecialUnitary_surjective (J : HermitianForm n K) :
    Function.Surjective (toProjectiveSpecialUnitary J) := by
  rintro ⟨_, A, hA, rfl⟩
  have hA' := (HermitianForm.mem_specialSubgroup_iff J A).mp hA
  have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
    have := congrArg Units.val hA'.2
    simpa using this
  let g : SpecialLinearGroup (Fin n) K := ⟨A, hdet⟩
  have hgA : Matrix.SpecialLinearGroup.toGL g = A := by
    ext
    rfl
  have hg : g ∈ specialUnitaryGroup (hermitianSesquilinear J) := by
    change Matrix.SpecialLinearGroup.toGL g ∈ unitaryGroup (hermitianSesquilinear J)
    rw [hgA, mem_unitaryGroup_hermitianSesquilinear_iff, HermitianForm.mem_unitarySubgroup_iff]
    exact hA'.1
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  change ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL g) = ProjGenLinGroup.mk A
  rw [hgA]

theorem ker_toProjectiveSpecialUnitary (J : HermitianForm n K) :
    (toProjectiveSpecialUnitary J).ker = unitaryScalars (hermitianSesquilinear J) := by
  ext g
  rw [MonoidHom.mem_ker, mem_unitaryScalars]
  change (⟨ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (g : SpecialLinearGroup (Fin n) K)),
    _⟩ : ProjectiveSpecialUnitaryMatrixGroup J) = 1 ↔ _
  rw [Subtype.ext_iff, Subgroup.coe_one, ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have := congrArg Units.val hc
    rw [Matrix.GeneralLinearGroup.coe_scalar] at this
    exact this.symm
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext : 1
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    simp [hc]

@[expose] def projectiveSpecialUnitaryMulEquiv (J : HermitianForm n K) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃*
      projectiveSpecialUnitaryGroup (hermitianSesquilinear J) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_toProjectiveSpecialUnitary J).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (toProjectiveSpecialUnitary_surjective J))).symm

end CFSG.ProperTwoGeneratedCore.HighRankPair
