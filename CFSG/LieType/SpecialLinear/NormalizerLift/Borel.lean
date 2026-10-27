module

public import CFSG.LieType.SpecialLinear.BorelStd

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {F : Type} [Field F] [Finite F]

instance finite_specialLinearGroup : Finite (SpecialLinearGroup (Fin n) F) :=
  Subtype.finite

omit [Finite F] in
theorem slFieldAut_mem_unitriangular (σ : F ≃+* F)
    {u : SpecialLinearGroup (Fin n) F} (hu : u ∈ unitriangular n F) :
    CatalogueBHigherLinearField.slFieldAut (Fin n) F σ u ∈ unitriangular n F := by
  constructor
  · intro i j hij
    change (CatalogueBHigherLinearField.slFieldEquiv (Fin n) σ u) i j = 0
    rw [CatalogueBHigherLinearField.slFieldEquiv_entry, hu.1 i j hij, map_zero]
  · intro i
    change (CatalogueBHigherLinearField.slFieldEquiv (Fin n) σ u) i i = 1
    rw [CatalogueBHigherLinearField.slFieldEquiv_entry, hu.2 i, map_one]

omit [Finite F] in
theorem slConjugation_mem_unitriangular_of_stdAut_zero
    (A : GL (Fin n) F) (σ : F ≃+* F)
    (h : ∀ u ∈ unitriangular n F,
      CFSG.QuasithinUnique.K1.stdAut A σ 0 u ∈ unitriangular n F) :
    ∀ u ∈ unitriangular n F,
      CatalogueBHigherLinearAction.slConjugation n F A u ∈ unitriangular n F := by
  intro v hv
  have hv' : CatalogueBHigherLinearField.slFieldAut (Fin n) F σ⁻¹ v ∈ unitriangular n F :=
    slFieldAut_mem_unitriangular σ⁻¹ hv
  have h1 : CatalogueBHigherLinearField.slFieldAut (Fin n) F σ
      (CatalogueBHigherLinearField.slFieldAut (Fin n) F σ⁻¹ v) = v := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have h2 := h (CatalogueBHigherLinearField.slFieldAut (Fin n) F σ⁻¹ v) hv'
  rwa [show CFSG.QuasithinUnique.K1.stdAut A σ 0 =
      CatalogueBHigherLinearAction.slConjugation n F A *
        CatalogueBHigherLinearField.slFieldAut (Fin n) F σ from by
        simp only [CFSG.QuasithinUnique.K1.stdAut, pow_zero, mul_one],
    MulAut.mul_apply, h1] at h2

theorem isUpperGL_of_stdAut_zero_mapsTo (A : GL (Fin n) F) (σ : F ≃+* F)
    (h : ∀ u ∈ unitriangular n F,
      CFSG.QuasithinUnique.K1.stdAut A σ 0 u ∈ unitriangular n F) :
    IsUpperGL A := by
  classical
  let U := unitriangular n F
  have hcA : ∀ u ∈ U, CatalogueBHigherLinearAction.slConjugation n F A u ∈ U :=
    slConjugation_mem_unitriangular_of_stdAut_zero A σ h
  have hcA_perm : U.map (CatalogueBHigherLinearAction.slConjugation n F A) = U := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨u, hu, rfl⟩
      exact hcA u hu
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hcA_inv : ∀ u ∈ U, (CatalogueBHigherLinearAction.slConjugation n F A)⁻¹ u ∈ U := by
    intro u hu
    have hmem : u ∈ U.map (CatalogueBHigherLinearAction.slConjugation n F A) := by
      rw [hcA_perm]
      exact hu
    obtain ⟨v, hv, hvu⟩ := hmem
    rw [← hvu]
    simpa using hv
  have hWinv : ∀ i : ℕ, ∀ u ∈ U,
      ∀ v ∈ (flagSpace n F i).map (Matrix.mulVecLin (A : Matrix (Fin n) (Fin n) F)),
        (u : Matrix (Fin n) (Fin n) F) *ᵥ v ∈
          (flagSpace n F i).map (Matrix.mulVecLin (A : Matrix (Fin n) (Fin n) F)) := by
    intro i u hu v hv
    obtain ⟨w, hw, rfl⟩ := hv
    let c : SpecialLinearGroup (Fin n) F :=
      (CatalogueBHigherLinearAction.slConjugation n F A)⁻¹ u
    refine ⟨((c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w, ?_, ?_⟩
    · exact flagSpace_invariant i (unitriangular_le_upperTriangular n F (hcA_inv u hu)) hw
    · have hcGL : SpecialLinearGroup.toGL c =
          A⁻¹ * SpecialLinearGroup.toGL u * A := by
        dsimp [c]
        change SpecialLinearGroup.toGL
          ((CatalogueBHigherLinearAction.slConjugation n F A)⁻¹ u) = _
        rw [show (CatalogueBHigherLinearAction.slConjugation n F A)⁻¹ =
          CatalogueBHigherLinearAction.slConjugation n F A⁻¹ from (map_inv _ _).symm]
        rw [CatalogueBHigherLinearAction.toGL_slConjugation]
        simp only [inv_inv]
      have hmat : (A : Matrix (Fin n) (Fin n) F) *
          ((c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (A : Matrix (Fin n) (Fin n) F) := by
        have hval := congrArg Units.val hcGL
        simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] at hval ⊢
        rw [hval, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          CFSG.QuasithinUnique.K1.coe_mul_coe_inv, Matrix.one_mul]
      change (A : Matrix (Fin n) (Fin n) F) *ᵥ
        (((c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w) =
        ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
          ((A : Matrix (Fin n) (Fin n) F) *ᵥ w)
      rw [Matrix.mulVec_mulVec, hmat, Matrix.mulVec_mulVec]
  have hAmap : ∀ i : ℕ, i ≤ n → (flagSpace n F i).map
      (Matrix.mulVecLin (A : Matrix (Fin n) (Fin n) F)) = flagSpace n F i := by
    intro i hi
    obtain ⟨m, hm, hW⟩ := eq_flagSpace_of_invariant (hWinv i)
    have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin n) (Fin n) F)) := by
      rw [Matrix.coe_mulVecLin]
      exact Matrix.mulVec_injective_iff_isUnit.2 A.isUnit
    have hfin : Module.finrank F ((flagSpace n F i).map
        (Matrix.mulVecLin (A : Matrix (Fin n) (Fin n) F))) = i :=
      (Submodule.equivMapOfInjective _ hinj (flagSpace n F i)).finrank_eq.symm.trans
        (finrank_flagSpace hi)
    have hmi : m = i := by
      have hcongr := congrArg (fun X : Submodule F (Fin n → F) => Module.finrank F X) hW
      rw [hfin, finrank_flagSpace hm] at hcongr
      exact hcongr.symm
    rw [hW, hmi]
  intro i j hij
  have hmem : (A : Matrix (Fin n) (Fin n) F) *ᵥ (Pi.single j 1) ∈ flagSpace n F (j + 1) := by
    rw [← hAmap (j + 1) (by omega)]
    refine Submodule.mem_map_of_mem ?_
    rw [mem_flagSpace]
    intro k hk
    rw [Pi.single_eq_of_ne]
    rintro rfl
    omega
  have hzero := (mem_flagSpace.mp hmem) i (by omega)
  rwa [Matrix.mulVec_single_one] at hzero

end CFSG.LieType.SpecialLinear
