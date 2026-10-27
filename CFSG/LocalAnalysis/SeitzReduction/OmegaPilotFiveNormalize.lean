module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveDescent
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveFamily

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCX plusCXstar
  automorphismTransport_apply)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.SeitzReduction.E7Pilot
open scoped Pointwise

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_mulEquiv_comp_eq_incl_four {σ : F ≃+* F} (hσ : orderOf σ = 2) {k : Subfield F}
    (hσk : ∀ x, x ∈ k ↔ σ x = x)
    {Kc : Type} [Group Kc] (ψ₀ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F))
    {τ : MulAut Kc} (hτ : τ * τ = 1) (hτout : τ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    {D' : Subgroup (fixedSubgroup τ)} (hD' : CFSG.IsComponent D') {g : ℕ}
    (hD'm : LieModel D' .POmegaPlus 4 2 g)
    {A : Type} [Group A] (ε : A →* Kc) (hε : Function.Injective ε)
    (hεr : ε.range = D'.map (fixedSubgroup τ).subtype)
    (j : A ≃* matrixProjectiveDerived (coordinateQuadPlus 4 k))
    (θ : MulAut Kc) (a : MulAut A) (hθa : ∀ x, θ (ε x) = ε (a x))
    (hγF : MulAut.congr j a • projectivePointFamily (coordinateQuadPlus 4 k) =
      projectivePointFamily (coordinateQuadPlus 4 k))
    (hγX : MulAut.congr j a • plusCX 4 k = plusCXstar 4 k (by norm_num))
    (hγX' : MulAut.congr j a • plusCXstar 4 k (by norm_num) = plusCX 4 k) :
    ∃ ψ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F),
      ∀ x, ψ (ε x) = incl k (isExtension_coordinateQuadPlus 4 k) (j x) := by
  have hext := isExtension_coordinateQuadPlus 4 k
  have : CharP k 2 := RingHom.charP k.subtype Subtype.val_injective 2
  set β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) :=
    MulAut.congr ψ₀ τ with hβdef
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hτ, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hτout
    have hτ1 : τ = 1 := (MulAut.congr ψ₀).injective (by rw [← hβdef, h, map_one])
    exact ⟨1, by rw [map_one, hτ1]⟩
  have hfix : fixedSubgroup β = (fixedSubgroup τ).map ψ₀.toMonoidHom :=
    ExcSelector.fixedSubgroup_congr ψ₀ τ
  let Φ : fixedSubgroup τ ≃* fixedSubgroup β :=
    ((fixedSubgroup τ).equivMapOfInjective ψ₀.toMonoidHom ψ₀.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  have hD'' : CFSG.IsComponent (D'.map Φ.toMonoidHom) := CatLeaf.isComponent_map_mulEquiv Φ hD'
  have hD''m : LieModel (D'.map Φ.toMonoidHom) .POmegaPlus 4 2 g :=
    LieType.CurtisTits.lieModel_of_mulEquiv (D'.equivMapOfInjective Φ.toMonoidHom Φ.injective)
      hD'm
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_fieldAutT_of_component_four hσ hβ hβ1 hD'' hD''m
  set σs := fieldAutT (coordinateQuadPlus 4 F) σ (coordinateQuadPlus_fieldMap 4 σ) with hσs
  set ψ₁ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F) := ψ₀.trans ψ with hψ₁
  have hσψ : ∀ x, σs (ψ x) = ψ (β x) := by
    intro x
    have h1 := congrArg (fun γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) =>
      γ (ψ x)) hψ
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
    exact h1.symm
  have hfixε : ∀ x, ψ₁ (ε x) ∈ fixedSubgroup σs := by
    intro x
    obtain ⟨d, -, hdx⟩ : ε x ∈ D'.map (fixedSubgroup τ).subtype := hεr ▸ ⟨x, rfl⟩
    have hτd : τ (ε x) = ε x := by
      rw [← hdx]
      exact d.2
    change σs (ψ (ψ₀ (ε x))) = ψ (ψ₀ (ε x))
    rw [hσψ]
    congr 1
    change ψ₀ (τ (ψ₀.symm (ψ₀ (ε x)))) = ψ₀ (ε x)
    rw [MulEquiv.symm_apply_apply, hτd]
  set ε' : matrixProjectiveDerived (coordinateQuadPlus 4 k) →*
      matrixProjectiveDerived (coordinateQuadPlus 4 F) :=
    (ψ₁.toMonoidHom.comp ε).comp j.symm.toMonoidHom with hε'
  have hε'inj : Function.Injective ε' := ψ₁.injective.comp (hε.comp j.symm.injective)
  have hJ : ⁅subfieldDerivedImage k hext, subfieldDerivedImage k hext⁆ =
      subfieldDerivedImage k hext :=
    commutator_range_of_commutator_top _ (commutator_top_coordinatePlus (by omega))
  obtain ⟨hQ, -⟩ := regular_coordinateQuadPlus 4 F (by omega)
  have hQne : ∃ v, coordinateQuadPlus 4 F v ≠ 0 :=
    exists_ne_zero_of_nondeg (by omega : 0 < 2 * 4) hQ
  have hcore := perfectCore_fixedSubgroup_fieldAutT (coordinateQuadPlus_fieldMap 4 σ) hσk hext
    hQne hJ
  have hperf : ⁅ε'.range, ε'.range⁆ = ε'.range :=
    commutator_range_of_commutator_top _ (commutator_top_coordinatePlus (by omega))
  have hle : ε'.range ≤ subfieldDerivedImage k hext := by
    rw [← hcore]
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ hperf
    rintro _ ⟨x, rfl⟩
    exact hfixε (j.symm x)
  have hιinj : Function.Injective (incl k hext) := incl_injective k hext (by omega)
  have hrange : ε'.range = (incl k hext).range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hε'inj).toEquiv]
  let δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 k)) :=
    ((MonoidHom.ofInjective hε'inj).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective hιinj).symm
  have hδ : ∀ x, incl k hext (δ x) = ε' x := by
    intro x
    have h1 := (MonoidHom.ofInjective hιinj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε'inj x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hψε : ∀ x, ψ₁ (ε x) = incl k hext (δ (j x)) := by
    intro x
    rw [hδ, hε']
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  set γ := MulAut.congr j a with hγ
  set θ' := MulAut.congr ψ₁ θ with hθ'
  have hθ'incl : ∀ z, θ' (incl k hext z) = incl k hext ((δ * γ * δ⁻¹) z) := by
    intro z
    obtain ⟨y, rfl⟩ := δ.surjective z
    have hjy : j.symm (γ y) = a (j.symm y) := by
      rw [hγ, automorphismTransport_apply, MulEquiv.symm_apply_apply]
    have hRHS : (δ * γ * δ⁻¹) (δ y) = δ (γ y) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [hRHS, hδ, hδ, hε']
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hθ', automorphismTransport_apply, MulEquiv.symm_apply_apply, hθa, hjy]
  have hγim : γ ∈ matrixProjectiveImage (coordinateQuadPlus 4 k) :=
    (mem_image_iff_smul_pointFamily le_rfl γ).2 hγF
  rcases mem_image_or_conj_mem_image_four δ γ hγF hγX hγX' with hδim | hμim
  ·
    obtain ⟨δ', hδ'⟩ := exists_mulAut_incl_comm_of_mem (K := F) (inv_mem hδim)
    refine ⟨ψ₁.trans δ', fun x => ?_⟩
    rw [MulEquiv.trans_apply, hψε, hδ', MulAut.inv_apply, MulEquiv.symm_apply_apply]
  ·
    obtain ⟨γ', hγ'⟩ := exists_mulAut_incl_comm_of_mem (K := F) hγim
    obtain ⟨μ', hμ'⟩ := exists_mulAut_incl_comm_of_mem (K := F) (inv_mem hμim)
    refine ⟨(ψ₁.trans (γ'.trans θ')).trans μ', fun x => ?_⟩
    simp only [MulEquiv.trans_apply]
    rw [hψε, hγ', hθ'incl, hμ']
    congr 1
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    simp only [MulAut.mul_apply]

end CFSG.SeitzReduction.OmegaPilot
