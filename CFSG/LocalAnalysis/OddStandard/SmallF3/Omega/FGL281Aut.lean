module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Grp

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter
open scoped commutatorElement

universe u

variable {K : Type u} [Field K]

@[expose] noncomputable def fgTwist (M : Matrix.GeneralLinearGroup (Fin 2) K) (σ : K ≃+* K) :
    Matrix.GeneralLinearGroup (Fin 2) K →* Matrix.GeneralLinearGroup (Fin 2) K :=
  (MulAut.conj M).toMonoidHom.comp (Matrix.GeneralLinearGroup.map σ.toRingHom)

theorem fgTwist_apply (M A : Matrix.GeneralLinearGroup (Fin 2) K) (σ : K ≃+* K) :
    fgTwist M σ A = M * Matrix.GeneralLinearGroup.map σ.toRingHom A * M⁻¹ := rfl

theorem fg_toPGL_action (g : PGL2 K) (σ : K ≃+* K) (x : PSL2 K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
      (semilinearAction K (SemidirectProduct.inl g * SemidirectProduct.inr σ) x) =
      g * (pgl2FieldAut K σ) (Matrix.ProjectiveSpecialLinearGroup.toPGL x) * g⁻¹ := by
  rw [map_mul, semilinearAction_inl, semilinearAction_inr, MulAut.mul_apply, toPGL_pglAction,
    psl2FieldAut_toPGL]

theorem fg_toPGL_action_mk (M : Matrix.GeneralLinearGroup (Fin 2) K) (σ : K ≃+* K)
    (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
      (semilinearAction K (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) *
        SemidirectProduct.inr σ) (QuotientGroup.mk B : PSL2 K)) =
      Matrix.ProjGenLinGroup.mk (fgTwist M σ (Matrix.SpecialLinearGroup.toGL B)) := by
  have h1 : (pgl2RingEquiv σ) (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL B)) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.toGL B)) :=
    pgl2RingEquiv_mk σ _
  rw [fg_toPGL_action, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, pgl2FieldAut_apply, h1,
    ← map_inv, ← map_mul, ← map_mul, fgTwist_apply]

theorem fg_twist_eq_mul_central {M : Matrix.GeneralLinearGroup (Fin 2) K} {σ : K ≃+* K}
    {B : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : semilinearAction K (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) *
        SemidirectProduct.inr σ) (QuotientGroup.mk B : PSL2 K) = QuotientGroup.mk B) :
    ∃ z ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K),
      fgTwist M σ (Matrix.SpecialLinearGroup.toGL B) = Matrix.SpecialLinearGroup.toGL B * z := by
  have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  rw [fg_toPGL_action_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk] at h1
  have h2 : Matrix.ProjGenLinGroup.mk ((Matrix.SpecialLinearGroup.toGL B)⁻¹ *
      fgTwist M σ (Matrix.SpecialLinearGroup.toGL B)) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  exact ⟨_, Matrix.ProjGenLinGroup.mk_eq_one.mp h2, by group⟩

theorem fg_lift_fixed {M : Matrix.GeneralLinearGroup (Fin 2) K} {σ : K ≃+* K}
    {P : Subgroup (PSL2 K)} (hP : ⁅P, P⁆ = P)
    (hfix : ∀ x ∈ P, semilinearAction K (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) *
        SemidirectProduct.inr σ) x = x) :
    ∀ x ∈ P, ∃ B : Matrix.SpecialLinearGroup (Fin 2) K, (QuotientGroup.mk B : PSL2 K) = x ∧
      fgTwist M σ (Matrix.SpecialLinearGroup.toGL B) = Matrix.SpecialLinearGroup.toGL B := by
  let T : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.GeneralLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.toGL
  let Fix : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    MonoidHom.eqLocus ((fgTwist M σ).comp T) T
  let N : Subgroup (PSL2 K) :=
    Fix.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
  have hcomm : ⁅P, P⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    obtain ⟨B₁, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨B₂, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z₁, hz₁, e₁⟩ := fg_twist_eq_mul_central (hfix _ hp)
    obtain ⟨z₂, hz₂, e₂⟩ := fg_twist_eq_mul_central (hfix _ hq)
    refine ⟨⁅B₁, B₂⁆, ?_, (map_commutatorElement _ B₁ B₂)⟩
    change (fgTwist M σ).comp T ⁅B₁, B₂⁆ = T ⁅B₁, B₂⁆
    rw [MonoidHom.comp_apply, map_commutatorElement, map_commutatorElement, e₁, e₂,
      fg_comm_mul_central hz₁ hz₂]
  intro x hx
  obtain ⟨B, hB, rfl⟩ := hcomm (hP.symm ▸ hx : x ∈ ⁅P, P⁆)
  exact ⟨B, rfl, hB⟩

variable [Finite K]

@[expose] noncomputable def fgFieldPart (K : Type u) [Field K] [Finite K] :
    MulAut (PSL2 K) →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom

theorem fg_exists_decomp (α : MulAut (PSL2 K)) :
    ∃ (M : Matrix.GeneralLinearGroup (Fin 2) K) (σ : K ≃+* K),
      α = semilinearAction K (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk M) *
        SemidirectProduct.inr σ) ∧ fgFieldPart K α = σ := by
  let d : PGammaL2 K := (semilinearEquivAut K).symm α
  obtain ⟨M, hM⟩ := Matrix.ProjGenLinGroup.mk_surjective d.left
  refine ⟨M, d.right, ?_, ?_⟩
  · rw [hM, SemidirectProduct.inl_left_mul_inr_right]
    exact ((semilinearEquivAut K).apply_symm_apply α).symm
  · exact congrFun SemidirectProduct.rightHom_eq_right d

end CFSG.OddStandard.SmallF3.Omega
