module

public import CFSG.LocalAnalysis.GLTheoremB.AutL34Bound
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {F : Type} [Field F] {K : Type} [Group K]

@[expose] noncomputable def t112_liftHom (e₁ : K ≃* SpecialLinearGroup (Fin 3) F) :
    MulAut K →* MulAut (projectiveSL 3 F) :=
  (descendAut 3 F).comp (MulAut.congr e₁).toMonoidHom

theorem t112_liftHom_injective (e₁ : K ≃* SpecialLinearGroup (Fin 3) F)
    (hperf : commutator K = ⊤) : Function.Injective (t112_liftHom e₁) := by
  rw [injective_iff_map_eq_one]
  intro ψ h
  apply CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut'_injective hperf
  rw [map_one]
  apply MulEquiv.ext
  intro y
  refine QuotientGroup.induction_on y ?_
  intro x
  have h1 := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (proj 3 F (e₁ x))) h
  simp only [t112_liftHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.one_apply,
    descendAut_proj, MulAut.congr_apply] at h1
  rw [proj_eq_proj_iff, scalars_eq_center] at h1
  have h2 : (e₁ x)⁻¹ * e₁ (ψ x) ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
    simpa using Subgroup.inv_mem _ h1
  have h3 : x⁻¹ * ψ x ∈ Subgroup.center K := by
    rw [← Subgroup.map_center_eq e₁] at h2
    obtain ⟨z, hz, hz'⟩ := h2
    have : z = x⁻¹ * ψ x := e₁.injective (by simpa using hz')
    rwa [← this]
  simp only [CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut', MonoidHom.coe_mk, OneHom.coe_mk,
    QuotientGroup.congr_mk, MulAut.one_apply]
  exact (QuotientGroup.eq.2 h3).symm

@[expose] noncomputable def stdAut (M : GL (Fin 3) F) (σ : F ≃+* F) :
    MulAut (SpecialLinearGroup (Fin 3) F) :=
  CatalogueBHigherLinearAction.slConjugation 3 F M *
    CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ *
    CatalogueBHigherLinearAction.slConjugation 3 F M⁻¹

theorem descendAut_stdAut (M : GL (Fin 3) F) (σ : F ≃+* F) :
    descendAut 3 F (stdAut M σ) = conjAut 3 F M * fieldAut 3 F σ * (conjAut 3 F M)⁻¹ := by
  rw [stdAut, map_mul, map_mul, ← map_inv]
  rfl

theorem toGL_stdAut (M : GL (Fin 3) F) (σ : F ≃+* F) (g : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.toGL (stdAut M σ g) =
      M * GeneralLinearGroup.map (σ : F →+* F) (M⁻¹ * SpecialLinearGroup.toGL g * M) * M⁻¹ := by
  change SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation 3 F M
    (CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ
      (CatalogueBHigherLinearAction.slConjugation 3 F M⁻¹ g))) = _
  rw [CatalogueBHigherLinearAction.toGL_slConjugation]
  have h1 : SpecialLinearGroup.toGL (CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ
      (CatalogueBHigherLinearAction.slConjugation 3 F M⁻¹ g)) =
      GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL
        (CatalogueBHigherLinearAction.slConjugation 3 F M⁻¹ g)) :=
    GeneralLinearGroup.ext fun _ _ => rfl
  rw [h1, CatalogueBHigherLinearAction.toGL_slConjugation, inv_inv]

theorem liftHom_conj (e₁ : K ≃* SpecialLinearGroup (Fin 3) F) (g : K) :
    t112_liftHom e₁ (MulAut.conj g) =
      conjAut 3 F (SpecialLinearGroup.toGL (e₁ g)) := by
  have h : MulAut.congr e₁ (MulAut.conj g) =
      CatalogueBHigherLinearAction.slConjugation 3 F (SpecialLinearGroup.toGL (e₁ g)) := by
    rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj]
    refine MulEquiv.ext fun y => ?_
    apply SpecialLinearGroup.toGL_injective
    rw [CatalogueBHigherLinearAction.toGL_slConjugation]
    simp
  change descendAut 3 F (MulAut.congr e₁ (MulAut.conj g)) = _
  rw [h]
  rfl

end CFSG.HardMathSupport.Solomon.Coordinator
