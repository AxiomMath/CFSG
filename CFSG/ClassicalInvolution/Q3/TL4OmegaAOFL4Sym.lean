module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFL4Aut
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFInn
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4GO3S
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4GO3N

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.L4

open Matrix CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 (kaGO3S_hom_units_trivial kaGO3SLift toGL_kaGO3SLift
  kaGO3S_isometry_of_odd ka_odd_mem_of_sq_mem KAL4Split ka_ringChar_ne_two_of_card_three
  kaGO3S_inv_transpose kaGO3STheta kaGO3STheta_mem kaGO3STheta_surj kaGO3STheta_mulVec
  kaGO3S_center_of_sandwich ka_orthData_nonsplit_three ka_noSplit_congr)
open CFSG.ComponentClassification.CatalogueBLinearHigherB (matrixQuadraticForm
  polarBilin_matrixQuadraticForm_nondegenerate)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  (split_four_determinant_form_isometry specialRho specialRho_apply)
open scoped MatrixGroups

section Graph

variable {F : Type} [Field F] [Finite F]

theorem oddCoreIn_fixed_of_model (h3 : Nat.card F = 3) (A : GL (Fin 4) F)
    {O : Type} [Group O] (θ : O →* GL (Fin 4) F) (ρ : SL(2, F) × SL(2, F) →* O)
    (hθI : ∀ d, θ d ∈ CFSG.ComponentClassification.CatalogueBGraphForm.isometryGroup 4 F A⁻¹)
    (hθS : ∀ X ∈ CFSG.ComponentClassification.CatalogueBGraphForm.isometryGroup 4 F A⁻¹,
      ∃ d, θ d = X)
    (hsq : ∀ d : O, d * d ∈ ρ.range)
    (hker : ∀ (z : SL(2, F) × SL(2, F)) (μ : Fˣ),
      θ (ρ z) = GeneralLinearGroup.scalar (Fin 4) μ →
        z.1 ∈ Subgroup.center SL(2, F) ∧ z.2 ∈ Subgroup.center SL(2, F)) :
    oddCoreIn (fixedSubgroup (conjAut 4 F A * dualAut 4 F)) = ⊥ := by
  have hdet : ∀ z, ((θ (ρ z) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    intro z
    have h := congrArg Units.val
      (kaGO3S_hom_units_trivial h3 (GeneralLinearGroup.det.comp (θ.comp ρ)) z)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h
  set lift := kaGO3SLift θ ρ hdet with hlift_def
  have hlift : ∀ z, SpecialLinearGroup.toGL (lift z) = θ (ρ z) := toGL_kaGO3SLift θ ρ hdet
  set β : SL(2, F) × SL(2, F) →* projectiveSL 4 F := (proj 4 F).comp lift with hβ
  have hβC : β.range ≤ fixedSubgroup (conjAut 4 F A * dualAut 4 F) := by
    rintro _ ⟨z, rfl⟩
    rw [Q3NM.mem_fixedSubgroup_iff]
    have hz : lift z ∈ isometrySL 4 A⁻¹ := by
      rw [isometrySL, Subgroup.mem_comap, hlift]
      exact hθI _
    show (conjAut 4 F A * dualAut 4 F) (proj 4 F (lift z)) = proj 4 F (lift z)
    rw [conjAut_mul_dualAut_proj, (graphLift_eq_iff A _).2 hz]
  have hNR : oddCoreIn (fixedSubgroup (conjAut 4 F A * dualAut 4 F)) ≤ β.range := by
    intro c hcN
    have hc := Q3NM.mem_fixedSubgroup_iff.1 (oddCoreIn_le _ hcN)
    have ho : Odd (orderOf c) :=
      (odd_card_oddCoreIn _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hcN)
    obtain ⟨g, rfl⟩ := proj_surjective 4 F c
    obtain ⟨d, hd⟩ := hθS _ (kaGO3S_isometry_of_odd h3 A g hc ho)
    obtain ⟨z, hz⟩ := hsq d
    have hz2 : lift z = g * g := by
      apply SpecialLinearGroup.toGL_injective
      simp only [hlift, hz, map_mul, hd]
    refine ka_odd_mem_of_sq_mem ?_ ho
    rw [← map_mul, ← hz2]
    exact ⟨z, rfl⟩
  refine CFSG.ComponentClassification.CatFactsL4U4.eq_bot_of_odd_block
    ⟨3, 1, Nat.prime_three, by decide, le_refl 1, by rw [h3]; norm_num⟩ β ?_ _ hNR ?_
    (odd_card_oddCoreIn _)
  · intro z hz
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hz)
    exact hker z c (by rw [← hlift]; exact Units.ext hc)
  · intro g hg r hr
    exact conj_mem_oddCoreIn (hβC hg) hr

theorem oddCoreIn_fixed_split (h3 : Nat.card F = 3) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) (hsp : KAL4Split A) :
    oddCoreIn (fixedSubgroup (conjAut 4 F A * dualAut 4 F)) = ⊥ := by
  have hK : ringChar F ≠ 2 := ka_ringChar_ne_two_of_card_three h3
  have hR := kaGO3S_inv_transpose A hA
  obtain ⟨S, hS2, hS0⟩ := hsp
  obtain ⟨ψ, e, -, -, hψ⟩ := split_four_determinant_form_isometry (matrixQuadraticForm A⁻¹)
    (polarBilin_matrixQuadraticForm_nondegenerate hK A⁻¹ hR) (Module.finrank_fin_fun F) S hS2 hS0
  refine oddCoreIn_fixed_of_model h3 A (kaGO3STheta hK hR e) specialRho (kaGO3STheta_mem hK hR e)
    (fun X hX => kaGO3STheta_surj hK hR e hX) (fun d => ?_) (fun z μ hz => ?_)
  · rw [← pow_two]
    exact CFSG.LocalAnalysis.ComponentInitial.determinant_sq_mem_specialImage d
  · have hmul := fun v => kaGO3STheta_mulVec hK hR e ψ hψ (specialRho z) v
    rw [hz] at hmul
    have hd : ∀ X : Matrix (Fin 2) (Fin 2) F, (specialRho z).val X = (μ : F) • X := by
      intro X
      apply ψ.symm.injective
      have h := hmul (ψ.symm X)
      rw [LinearEquiv.apply_symm_apply] at h
      rw [map_smul, ← h]
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    exact kaGO3S_center_of_sandwich μ.ne_zero fun X => by rw [← specialRho_apply]; exact hd X

theorem oddCoreIn_fixed_nonsplit (h3 : Nat.card F = 3) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) (hns : ¬ KAL4Split A) :
    oddCoreIn (fixedSubgroup (conjAut 4 F A * dualAut 4 F)) = ⊥ := by
  have hK : ringChar F ≠ 2 := ka_ringChar_ne_two_of_card_three h3
  have hR := inv_transpose_of_transpose_eq A hA
  obtain ⟨P, w, hw, hP⟩ := exists_orth_normal_form hK (by norm_num : 3 ≤ 4) A⁻¹ hR
  set H := P⁻¹ with hH
  have hHA : H * A * GeneralLinearGroup.inverseTranspose H⁻¹ = (diagGL hw.1)⁻¹ := by
    have hT : CFSG.ComponentClassification.CatalogueBGraphForm.glTranspose 4 F P * A⁻¹ * P =
        diagGL hw.1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul,
        CFSG.ComponentClassification.CatalogueBGraphForm.glTranspose_matrix, coe_diagGL]
      exact hP
    have hT' : CFSG.ComponentClassification.CatalogueBGraphForm.glTranspose 4 F P =
        (GeneralLinearGroup.inverseTranspose P)⁻¹ := rfl
    rw [← hT, hT', hH, inv_inv]
    group
  have hsym : ((diagGL hw.1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = diagGL hw.1 := by
    rw [coe_diagGL, diagonal_transpose]
  have hdata := ka_orthData_nonsplit_three h3 _ hsym
    (ka_noSplit_congr (R := A⁻¹) (P := P) (by rw [coe_diagGL]; exact hP) hns)
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F) (n := 4)
    (by norm_num)
  have key := oddCoreIn_fixed_eq_bot_of_inn hinj _
    (orth_oddCoreIn_eq_bot_of_data hK (by norm_num) hinj le_rfl hw hdata)
  have h1 := oddCoreIn_fixed_conj_eq_bot (conjAut 4 F H)⁻¹ _ key
  have h2 : (conjAut 4 F H)⁻¹ * (conjAut 4 F (diagGL hw.1)⁻¹ * dualAut 4 F) *
      (conjAut 4 F H)⁻¹⁻¹ = conjAut 4 F A * dualAut 4 F := by
    rw [← hHA, ← conjAut_mul_conjAut_dualAut_mul_inv]
    group
  rwa [h2] at h1

theorem pslSymStatement_of_card (h3 : Nat.card F = 3) : PSLSymStatement F := by
  intro A hA
  by_cases hs : KAL4Split A
  · exact oddCoreIn_fixed_split h3 A hA hs
  · exact oddCoreIn_fixed_nonsplit h3 A hA hs

end Graph

section Model


theorem outerFixedOddFree_psl4 : OuterFixedOddFree .PSL 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by simpa using GaloisField.card 3 1 one_ne_zero
  exact outerFixedOddFree_psl4_of (pslSymStatement_of_card hF)

end Model

end CFSG.ClassicalInvolution.Q3.TL4.L4
