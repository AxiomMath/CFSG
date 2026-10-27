module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZEps

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.Bal207.D4Graph CFSG.ComponentClassification.CatalogueBOrthogonalPointData
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner


theorem congr_congr_symm {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (t : MulAut H) :
    MulAut.congr ψ (MulAut.congr ψ.symm t) = t :=
  MulEquiv.ext fun x => by simp [MulAut.congr_apply]

theorem d3FieldInvolution_holds : D3FieldInvolution := by
  intro K _ _ n hK t ht3 htE z hz2 hzI hzt A hA hAt hAz
  haveI := charP_three_of_card hK
  have hn : 1 ≤ n := one_le_of_card_field hK
  have hrc : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  let ψ : adjointGroup Tag.D4 K ≃* D4Model K := coordinatePlusWitnessEquiv K (isoAdj K).symm
  let φ : D4Model K ≃* adjointGroup Tag.D4 K := ψ.symm
  set α : MulAut (adjointGroup Tag.D4 K) := MulAut.congr φ t with hα
  set ζ : MulAut (adjointGroup Tag.D4 K) := MulAut.congr φ z with hζdef
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, ht3, map_one]
  have hζ2 : ζ * ζ = 1 := by rw [hζdef, ← map_mul, ← pow_two, hz2, map_one]
  have hζα : ζ * α = α * ζ := by rw [hζdef, hα, ← map_mul, ← map_mul, hzt]
  have htα : t = MulAut.congr ψ α := (congr_congr_symm ψ t).symm
  have hαnot : ∀ x : adjointGroup Tag.D4 K, α ≠ MulAut.conj x := by
    intro x hx
    apply htE
    rw [htα, hx, d3f_congr_conj]
    exact CFSG.HardMathSupport.Timmesfeld.DefChar.Orth.inner_mem_matrixProjectiveImage _ _
  obtain ⟨g, a, σ, ε, hε3, -, hαform⟩ := CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma α hα3
  have hε0 : ε ≠ 0 := eps_ne_zero hK ht3 htE g a σ ε (by rw [htα, hαform])
  have hε : ε = 1 ∨ ε = 2 := by omega
  obtain ⟨c, a_z, σ_z, hσz2, hζ⟩ := z_normal_form α ζ g a σ ε hε hαform hζ2 hζα
  by_cases hσ1 : σ_z = 1
  · exfalso
    subst hσ1
    obtain ⟨y, hy⟩ := diag_case_inner hrc α ζ g c a a_z σ ε hε hαform hζ hζα
    apply hzI
    refine ⟨ψ y, ?_⟩
    have h1 : z = MulAut.congr ψ ζ := (congr_congr_symm ψ z).symm
    rw [h1, hy, d3f_congr_conj]
  · have hA' := d3f_isElemAbelian_map φ hA
    have hfixα : ∀ x ∈ A.map φ.toMonoidHom, α x = x := by
      rintro _ ⟨x, hx, rfl⟩
      change α (φ x) = φ x
      rw [hα, MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hAt x hx]
    have hfixζ : ∀ x ∈ A.map φ.toMonoidHom, ζ x = x := by
      rintro _ ⟨x, hx, rfl⟩
      change ζ (φ x) = φ x
      rw [hζdef, MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hAz x hx]
    have hcard : Nat.card (A.map φ.toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective φ.injective
    have hb := field_case_card_le hn hK σ_z hσz2 hσ1 ζ c a_z hζ hζ2 α hα3 hαnot hζα _ hA' hfixζ hfixα
    rwa [hcard] at hb

end CFSG.LocalAnalysis.GLTheoremA
