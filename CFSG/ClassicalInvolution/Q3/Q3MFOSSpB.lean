module

public import CFSG.ClassicalInvolution.Q3.Q3MFOSSpA
public import CFSG.ClassicalInvolution.Q3.Q3MFOSAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFO.Sp

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ComponentClassification.CatalogueBSymplecticTwo
  (pointParabolics planeParabolics typeKernel mem_typeKernel type_kernel)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj stabilizer mem_stabilizer)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped Matrix MatrixGroups

section Kernel

variable {F : Type} [Field F] [Finite F]

abbrev line1 (F : Type) [Field F] : Submodule F (Fin 2 ⊕ Fin 2 → F) :=
  Submodule.span F {(Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F)}

theorem finrank_line1 : Module.finrank F (line1 F) = 1 := by
  apply finrank_span_singleton
  intro h
  have := congrFun h (Sum.inl 1)
  simp at this

theorem tU_mem_stabilizer_line1 : tU F ∈ stabilizer 2 F (line1 F) := by
  have h : Matrix.mulVecLin ((tU F : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Pi.single (Sum.inl 1) 1) =
        Pi.single (Sum.inl 1) 1 := by
    rw [Matrix.mulVecLin_apply]
    change mat 2 F (tU F) *ᵥ _ = _
    rw [mat_tU, mulVec_tU]
    simp
  rw [mem_stabilizer, Submodule.map_span, Set.image_singleton, h]

theorem tL_mem_stabilizer_line1 : tL F ∈ stabilizer 2 F (line1 F) := by
  have h : Matrix.mulVecLin ((tL F : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Pi.single (Sum.inl 1) 1) =
        Pi.single (Sum.inl 1) 1 := by
    rw [Matrix.mulVecLin_apply]
    change mat 2 F (tL F) *ᵥ _ = _
    rw [mat_tL, mulVec_tL]
    simp
  rw [mem_stabilizer, Submodule.map_span, Set.image_singleton, h]

theorem mulVec_mem_of_mem_stabilizer {W : Submodule F (Fin 2 ⊕ Fin 2 → F)} {g : StatedSp 2 F}
    (hg : g ∈ stabilizer 2 F W) {w : Fin 2 ⊕ Fin 2 → F} (hw : w ∈ W) :
    mat 2 F g *ᵥ w ∈ W := by
  rw [mem_stabilizer] at hg
  have h := Submodule.mem_map_of_mem (f := Matrix.mulVecLin ((g : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hw
  rw [hg, Matrix.mulVecLin_apply] at h
  exact h

theorem mem_typeKernel_of_fixes {α : MulAut (StatedProj (StatedSp 2 F))}
    (hU : α (proj 2 F (tU F)) = proj 2 F (tU F)) (hL : α (proj 2 F (tL F)) = proj 2 F (tL F)) :
    α ∈ typeKernel F := by
  obtain ⟨p, hchar⟩ := CharP.exists F
  have hp : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  obtain ⟨hdich, -⟩ := type_kernel (K := F) p
  obtain ⟨-, -, h | h⟩ := hdich α
  · exact mem_typeKernel.mpr h.1
  · exfalso
    have hM1 : projStabilizer 2 F (line1 F) ∈ pointParabolics F :=
      ⟨line1 F, finrank_line1, rfl⟩
    have hmem : (projStabilizer 2 F (line1 F)).map α.toMonoidHom ∈ planeParabolics F := by
      rw [← h.1]
      exact Set.mem_image_of_mem _ hM1
    obtain ⟨W, hWiso, hWdim, hW⟩ := hmem
    have hstab : ∀ g : StatedSp 2 F, g ∈ stabilizer 2 F (line1 F) →
        α (proj 2 F g) = proj 2 F g → g ∈ stabilizer 2 F W := by
      intro g hg hαg
      have h1 : proj 2 F g ∈ (projStabilizer 2 F (line1 F)).map α.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨proj 2 F g, Subgroup.mem_map_of_mem _ hg, hαg⟩
      rw [hW] at h1
      have h2 : g ∈ (projStabilizer 2 F W).comap (proj 2 F) := h1
      rwa [comap_projStabilizer] at h2
    have hsU := hstab _ tU_mem_stabilizer_line1 hU
    have hsL := hstab _ tL_mem_stabilizer_line1 hL
    refine no_invariant_isotropic_plane W hWiso hWdim (fun w hw => ?_) (fun w hw => ?_)
    · simpa [mat_tU] using mulVec_mem_of_mem_stabilizer hsU hw
    · simpa [mat_tL] using mulVec_mem_of_mem_stabilizer hsL hw

end Kernel

section Inner

open CFSG.ClassicalGroups.Orthogonal.Small (three_eq_zero_two_ne_zero_of_card_eq_three)
open CFSG.ComponentClassification.CatalogueBSymplecticTwo (kernel_generation)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
  (simMat simInv simInv_mul mat_conjSp)

variable {F : Type} [Field F] [Finite F]

theorem exists_conj_of_fixes (hF : Nat.card F = 3) {ρ : MulAut (StatedProj (StatedSp 2 F))}
    (hU : ρ (proj 2 F (tU F)) = proj 2 F (tU F)) (hL : ρ (proj 2 F (tL F)) = proj 2 F (tL F)) :
    ∃ s : StatedSp 2 F, ρ = MulAut.conj (proj 2 F s) := by
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hF
  obtain ⟨-, hgen, -⟩ := kernel_generation (K := F)
  obtain ⟨A, σ, hρ⟩ := hgen ρ (mem_typeKernel_of_fixes hU hL)
  rw [ringEquiv_eq_one hF σ, map_one, mul_one] at hρ
  have hUc := conjSp_eq_of_conjAut_eq h2 A (tU_pow_three h3) (by rw [← hρ]; exact hU)
  have hLc := conjSp_eq_of_conjAut_eq h2 A (tL_pow_three h3) (by rw [← hρ]; exact hL)
  have hcU := mul_eq_of_conjSp_eq' A hUc
  have hcL := mul_eq_of_conjSp_eq' A hLc
  rw [mat_tU, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hcU
  rw [mat_tL, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hcL
  have hAμ : (simMat A)ᵀ * gram F 2 * simMat A =
      ((multiplier 2 F A : Fˣ) : F) • gram F 2 := multiplier_spec A
  obtain ⟨l, hl0, hμ⟩ := multiplier_eq_sq_of_commute (simMat A) (simInv A) _ (simInv_mul A)
    (add_left_cancel hcU) (add_left_cancel hcL) hAμ
  have hl' : l⁻¹ * l⁻¹ * (l * l) = 1 := by field_simp
  have hM : (l⁻¹ • simMat A)ᵀ * gram F 2 * (l⁻¹ • simMat A) = gram F 2 := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAμ,
      hμ, smul_smul, hl', one_smul]
  set s : StatedSp 2 F := ofSymplecticMat (l⁻¹ • simMat A) hM with hs
  have hconj : ∀ g : StatedSp 2 F, conjSp 2 F A g = s * g * s⁻¹ := by
    intro g
    refine eq_mul_inv_of_mul_eq (mat_injective ?_)
    rw [map_mul, map_mul, mat_conjSp, hs, mat_ofSymplecticMat, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc, simInv_mul, Matrix.mul_one]
  refine ⟨s, ?_⟩
  rw [hρ]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) x
  rw [conjAut_proj, hconj, MulAut.conj_apply, map_mul, map_mul, map_inv]

end Inner

section Quotient

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def centralQuotEquiv :
    StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F) :=
  QuotientGroup.quotientMulEquivOfEq (CFSG.LieType.Universal.Symplectic.center_eq 2 F)

theorem centralQuotEquiv_mk (x : StatedSp 2 F) :
    centralQuotEquiv (QuotientGroup.mk x) = proj 2 F x := rfl

theorem centralQuotEquiv_symm_proj (x : StatedSp 2 F) :
    centralQuotEquiv.symm (proj 2 F x) = QuotientGroup.mk x :=
  centralQuotEquiv.symm_apply_eq.mpr (centralQuotEquiv_mk x).symm

theorem exists_conj_of_fixes_quot (hF : Nat.card F = 3)
    {ρ : MulAut (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F))}
    (hU : ρ (QuotientGroup.mk (tU F)) = QuotientGroup.mk (tU F))
    (hL : ρ (QuotientGroup.mk (tL F)) = QuotientGroup.mk (tL F)) :
    ∃ s : StatedSp 2 F, ρ = MulAut.conj (QuotientGroup.mk s) := by
  obtain ⟨s, hs⟩ := exists_conj_of_fixes hF (ρ := MulAut.congr centralQuotEquiv ρ)
    (by
      change centralQuotEquiv (ρ (centralQuotEquiv.symm (proj 2 F (tU F)))) = _
      rw [centralQuotEquiv_symm_proj, hU]
      rfl)
    (by
      change centralQuotEquiv (ρ (centralQuotEquiv.symm (proj 2 F (tL F)))) = _
      rw [centralQuotEquiv_symm_proj, hL]
      rfl)
  refine ⟨s, MulEquiv.ext fun x => ?_⟩
  have h := congrArg (fun φ => centralQuotEquiv.symm (φ (centralQuotEquiv x))) hs
  simpa [MulAut.congr_apply, MulAut.conj_apply, centralQuotEquiv_symm_proj] using h

end Quotient

end CFSG.ClassicalInvolution.Q3.Q3MFO.Sp
