module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem eq_one_of_centerDescend_eq_one {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {α : MulAut Y} (h : centerDescend Y α = 1) : α = 1 := by
  have : Group.IsPerfect Y := (Group.isPerfect_def (G := Y)).2 hY.1
  refine CFSG.RankThree.PartTwo.Sec4.mulAut_eq_of_inv_mul_mem_center (β := 1) fun s => ?_
  have h1 := congrArg (fun τ : MulAut (Y ⧸ Subgroup.center Y) => τ (s : Y ⧸ Subgroup.center Y)) h
  simp only [centerDescend_mk, MulAut.one_apply] at h1
  have := QuotientGroup.eq.mp h1.symm
  simpa using this

theorem eq_one_of_isField_mem_inndiag {M : Type*} [Group M] (P : PinnedAut M) (hS : P.Separated)
    (hN : P.inndiag.Normal) {φ : MulAut M} (hφ : φ ∈ P.field) (γ : MulAut M)
    (h : γ * φ * γ⁻¹ ∈ P.inndiag) : γ * φ * γ⁻¹ = 1 := by
  have h1 := hN.conj_mem _ h γ⁻¹
  have h2 : γ⁻¹ * (γ * φ * γ⁻¹) * γ⁻¹⁻¹ = φ := by group
  rw [h2] at h1
  rw [hS.field_inter φ hφ h1]
  group

theorem descend_apply_mk {Y P : Type*} [Group Y] [Group P] (e : (Y ⧸ Subgroup.center Y) ≃* P)
    (α : MulAut Y) (y : Y) :
    MulAut.congr e (centerDescend Y α) (e (QuotientGroup.mk y)) = e (QuotientGroup.mk (α y)) :=
  (descend_compat e α y).symm

@[expose] noncomputable def psiO (F : Type) [Field F] :
    CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F) ≃* projectiveSL 3 F :=
  psiPSL F

@[expose] noncomputable def mkO (F : Type) [Field F] (s : Matrix.SpecialLinearGroup (Fin 3) F) :
    CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F) :=
  QuotientGroup.mk (specialLinearGroupEquivStatedSL 3 F s)

theorem psiO_mkO (F : Type) [Field F] (s : Matrix.SpecialLinearGroup (Fin 3) F) :
    psiO F (mkO F s) = proj 3 F s :=
  psiPSL_mk F s

theorem mkO_surjective (F : Type) [Field F] :
    Function.Surjective (mkO F) := fun x => by
  obtain ⟨s, hs⟩ := proj_surjective 3 F (psiO F x)
  refine ⟨s, (psiO F).injective ?_⟩
  rw [psiO_mkO, hs]

theorem congr_psiO_of_entrywise {F : Type} [Field F] {σ : F ≃+* F}
    {φ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F))} (h : IsEntrywiseAutPSL σ φ) :
    MulAut.congr (psiO F) φ = fieldAut 3 F σ := by
  ext x
  obtain ⟨s, rfl⟩ := proj_surjective 3 F x
  rw [fieldAut_proj]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  have h1 : (psiO F).symm (proj 3 F s) = mkO F s := by
    rw [MulEquiv.symm_apply_eq, psiO_mkO]
  rw [h1]
  have h2 : φ (mkO F s) = mkO F (Matrix.SpecialLinearGroup.map σ.toRingHom s) :=
    h (specialLinearGroupEquivStatedSL 3 F s)
      (specialLinearGroupEquivStatedSL 3 F (Matrix.SpecialLinearGroup.map σ.toRingHom s)) (by
        simp only [specialLinearGroupEquivStatedSL_coe]
        rfl)
  rw [h2, psiO_mkO]

theorem fieldAutPSL3_data {Y : Type*} [Group Y] {α : MulAut Y} (h : IsFieldAutPSL3 α) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 F)
      (σ : F ≃+* F) (γ : MulAut (projectiveSL 3 F)),
      MulAut.congr e (centerDescend Y α) = γ * fieldAut 3 F σ * γ⁻¹ := by
  obtain ⟨F, _, _, θ, σ, φ, γ, hφ, hα⟩ := h
  refine ⟨F, inferInstance, inferInstance, θ.trans (psiO F), σ,
    MulAut.congr (psiO F) γ, ?_⟩
  ext x
  obtain ⟨z, rfl⟩ := (θ.trans (psiO F)).surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  rw [descend_apply_mk (θ.trans (psiO F)) α y, ← congr_psiO_of_entrywise hφ]
  simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.congr_apply,
    MulEquiv.symm_apply_apply]
  rw [hα y]
  simp [MulAut.mul_apply]

section Unitary

variable {p f : ℕ} {F : Type} [Field F]

@[expose] noncomputable def psuO (h : UnitaryFieldData p f F) :
    unitaryPSU h 3 ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F) :=
  unitaryPSUEquiv h (n := 3) (by norm_num)

theorem psuO_proj (h : UnitaryFieldData p f F) (g : unitarySU p f F 3) :
    psuO h (unitaryProj h 3 g) = QuotientGroup.mk g :=
  unitaryPSUEquiv_unitaryProj h (n := 3) (by norm_num) g

theorem congr_psuO_of_entrywise (h : UnitaryFieldData p f F) {σ : F ≃+* F}
    {φ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F))}
    (hφ : IsEntrywiseAutPSU (p ^ f) σ φ) :
    MulAut.congr (psuO h).symm φ = psuField h σ := by
  ext x
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
  simp only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply]
  have h2 : φ (psuO h (unitaryProj h 3 g)) = psuO h (unitaryProj h 3 (suField h σ g)) := by
    rw [psuO_proj, psuO_proj]
    exact hφ g (suField h σ g) (by rw [coe_suField, UnitaryHigher.coe_glAut])
  rw [h2, MulEquiv.symm_apply_apply]
  exact (psuField_mk σ g).symm

theorem fieldAutPSU3_data {Y : Type*} [Group Y] {α : MulAut Y} (h : IsFieldAutPSU3 α) :
    ∃ (p f : ℕ) (F : Type) (_ : Field F) (hF : UnitaryFieldData p f F)
      (e : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3) (σ : F ≃+* F)
      (γ : MulAut (unitaryPSU hF 3)), Odd (orderOf σ) ∧
      MulAut.congr e (centerDescend Y α) = γ * psuField hF σ * γ⁻¹ := by
  obtain ⟨F, _, _, q, θ, σ, φ, γ, hcard, hodd, hφ, hα⟩ := h
  obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
  refine ⟨p, f, F, inferInstance, hF, θ.trans (psuO hF).symm, σ,
    MulAut.congr (psuO hF).symm γ, hodd, ?_⟩
  ext x
  obtain ⟨z, rfl⟩ := (θ.trans (psuO hF).symm).surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  rw [descend_apply_mk (θ.trans (psuO hF).symm) α y, ← congr_psuO_of_entrywise hF hφ]
  simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.congr_apply,
    MulEquiv.symm_symm]
  rw [hα y]
  simp [MulAut.mul_apply]

end Unitary

end CFSG.HardMathSupport.Solomon.Coordinator
