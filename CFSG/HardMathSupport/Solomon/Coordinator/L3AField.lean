module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3ABridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem isEntrywise_of_congr_psiO {F : Type} [Field F] {σ : F ≃+* F}
    {φ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F))}
    (h : MulAut.congr (psiO F) φ = fieldAut 3 F σ) : IsEntrywiseAutPSL σ φ := by
  intro A A' hA
  obtain ⟨s, rfl⟩ := (specialLinearGroupEquivStatedSL 3 F).surjective A
  have hA' : A' = specialLinearGroupEquivStatedSL 3 F
      (Matrix.SpecialLinearGroup.map σ.toRingHom s) := by
    apply Subtype.ext
    apply Units.ext
    rw [specialLinearGroupEquivStatedSL_coe, Matrix.SpecialLinearGroup.map_apply_coe]
    have := hA
    rw [specialLinearGroupEquivStatedSL_coe] at this
    exact this
  subst hA'
  change φ (mkO F s) = mkO F (Matrix.SpecialLinearGroup.map σ.toRingHom s)
  apply (psiO F).injective
  have h1 := congrArg (fun τ : MulAut (projectiveSL 3 F) => τ (psiO F (mkO F s))) h
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, psiO_mkO,
    fieldAut_proj] at h1
  rw [psiO_mkO]
  exact h1

theorem isEntrywise_of_congr_psuO {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)
    {σ : F ≃+* F} {φ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F))}
    (h : MulAut.congr (psuO hF).symm φ = psuField hF σ) : IsEntrywiseAutPSU (p ^ f) σ φ := by
  intro A A' hA
  let B : ↥(unitarySU p f F 3) := A
  let B' : ↥(unitarySU p f F 3) := A'
  have hB' : B' = suField hF σ B := Subtype.ext (by
    rw [coe_suField]
    exact Units.ext (by rw [UnitaryHigher.coe_glAut]; exact hA))
  have h1 := congrArg (fun τ : MulAut (unitaryPSU hF 3) => τ (unitaryProj hF 3 B)) h
  simp only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply] at h1
  rw [psuO_proj] at h1
  have h2 : φ (QuotientGroup.mk B) = psuO hF (unitaryProj hF 3 (suField hF σ B)) := by
    apply (psuO hF).symm.injective
    rw [MulEquiv.symm_apply_apply]
    exact h1.trans (psuField_mk σ B)
  show φ (QuotientGroup.mk B) = QuotientGroup.mk B'
  rw [h2, hB', psuO_proj]

theorem isFieldAutPSL3_of_data {Y : Type*} [Group Y] {α : MulAut Y} {F : Type} [Field F] [Finite F]
    (e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 F) (σ : F ≃+* F)
    (γ : MulAut (projectiveSL 3 F))
    (h : MulAut.congr e (centerDescend Y α) = γ * fieldAut 3 F σ * γ⁻¹) : IsFieldAutPSL3 α := by
  refine ⟨F, inferInstance, inferInstance, e.trans (psiO F).symm, σ,
    MulAut.congr (psiO F).symm (fieldAut 3 F σ), MulAut.congr (psiO F).symm γ,
    isEntrywise_of_congr_psiO (by ext x; simp [MulAut.congr_apply]), fun y => ?_⟩
  have h1 := descend_apply_mk e α y
  rw [h] at h1
  have key : (MulAut.congr (psiO F).symm γ * MulAut.congr (psiO F).symm (fieldAut 3 F σ) *
      (MulAut.congr (psiO F).symm γ)⁻¹) =
      MulAut.congr (psiO F).symm (γ * fieldAut 3 F σ * γ⁻¹) := by
    simp only [map_mul, map_inv]
  rw [key]
  simp only [MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.symm_symm,
    MulEquiv.apply_symm_apply]
  rw [h1]

theorem isFieldAutPSU3_of_data {Y : Type*} [Group Y] {α : MulAut Y} {p f : ℕ} {F : Type}
    [Field F] (hF : UnitaryFieldData p f F)
    (e : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3) (σ : F ≃+* F) (hodd : Odd (orderOf σ))
    (γ : MulAut (unitaryPSU hF 3))
    (h : MulAut.congr e (centerDescend Y α) = γ * psuField hF σ * γ⁻¹) : IsFieldAutPSU3 α := by
  have := hF.finite
  refine ⟨F, inferInstance, inferInstance, p ^ f, e.trans (psuO hF), σ,
    MulAut.congr (psuO hF) (psuField hF σ), MulAut.congr (psuO hF) γ,
    by rw [hF.card, pow_mul'], hodd,
    isEntrywise_of_congr_psuO hF (by ext x; simp [MulAut.congr_apply]), fun y => ?_⟩
  have h1 := descend_apply_mk e α y
  rw [h] at h1
  have key : (MulAut.congr (psuO hF) γ * MulAut.congr (psuO hF) (psuField hF σ) *
      (MulAut.congr (psuO hF) γ)⁻¹) =
      MulAut.congr (psuO hF) (γ * psuField hF σ * γ⁻¹) := by
    simp only [map_mul, map_inv]
  rw [key]
  simp only [MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.symm_apply_apply]
  rw [h1]

end CFSG.HardMathSupport.Solomon.Coordinator
