module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Mat2Omega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {U U' : Type} [AddCommGroup U] [Module (ZMod 3) U] [FiniteDimensional (ZMod 3) U]
  [AddCommGroup U'] [Module (ZMod 3) U'] [FiniteDimensional (ZMod 3) U']
  {R : QuadraticForm (ZMod 3) U} {R' : QuadraticForm (ZMod 3) U'}

theorem orthogonalGroupCongr_piOrth (e : R.IsometryEquiv R') :
    TauCeti.QuadraticMap.orthogonalGroupCongr e (piOrth R) = piOrth R' := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply, coe_piOrth_apply, map_neg,
    LinearEquiv.apply_symm_apply, coe_piOrth_apply]

theorem map_omegaGroup_orthogonalGroupCongr (hR : R.Nondegenerate) (hR' : R'.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) U) (e : R.IsometryEquiv R') :
    (omegaGroup hR).map (TauCeti.QuadraticMap.orthogonalGroupCongr e).toMonoidHom =
      omegaGroup hR' := by
  have h2' : 2 ≤ Module.finrank (ZMod 3) U' := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact h2
  rw [omegaGroup_eq_commutator hR h2, omegaGroup_eq_commutator hR' h2', commutator_def,
    commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (TauCeti.QuadraticMap.orthogonalGroupCongr e).surjective]

theorem mem_omegaGroup_orthogonalGroupCongr_iff (hR : R.Nondegenerate) (hR' : R'.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) U) (e : R.IsometryEquiv R') (x : OGroup R) :
    TauCeti.QuadraticMap.orthogonalGroupCongr e x ∈ omegaGroup hR' ↔ x ∈ omegaGroup hR := by
  rw [← map_omegaGroup_orthogonalGroupCongr hR hR' h2 e]
  exact Subgroup.mem_map_iff_mem (TauCeti.QuadraticMap.orthogonalGroupCongr e).injective

theorem exists_pocket_plus4 (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) U = 4)
    (hsign : quadSign R = 1) :
    ∃ K : Subgroup (OGroup R), piOrth R ∈ K ∧ K ≤ omegaGroup hR ∧
      (K.subgroupOf (omegaGroup hR)).Normal ∧ Nonempty (K ≃* SL2F3) := by
  obtain ⟨e⟩ := equivalent_of_quadSign_eq detForm_nondegenerate hR
    (finrank_mat2.trans hdim.symm) (quadSign_detForm.trans hsign.symm)
  obtain ⟨K, hpi, hKle, hKn, ⟨f⟩⟩ := exists_pocket_model
  have h2 : 2 ≤ Module.finrank (ZMod 3) Mat2 := by
    rw [finrank_mat2]
    norm_num
  have hΩ := mem_omegaGroup_orthogonalGroupCongr_iff detForm_nondegenerate hR h2 e
  refine ⟨K.map (TauCeti.QuadraticMap.orthogonalGroupCongr e).toMonoidHom,
    ⟨piOrth detForm, hpi, orthogonalGroupCongr_piOrth e⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact (hΩ k).mpr (hKle hk)
  · constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨n₀, hn₀, hnφ⟩ := hn
    have hg₀ : (TauCeti.QuadraticMap.orthogonalGroupCongr e).symm (g : OGroup R) ∈
        omegaGroup detForm_nondegenerate := by
      rw [← hΩ, MulEquiv.apply_symm_apply]
      exact g.2
    have hc := hKn.conj_mem ⟨n₀, hKle hn₀⟩ (Subgroup.mem_subgroupOf.mpr hn₀)
      ⟨(TauCeti.QuadraticMap.orthogonalGroupCongr e).symm (g : OGroup R), hg₀⟩
    rw [Subgroup.mem_subgroupOf] at hc
    refine ⟨_, hc, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] at hnφ ⊢
    rw [hnφ]
  · exact ⟨(Subgroup.equivMapOfInjective K
      (TauCeti.QuadraticMap.orthogonalGroupCongr e).toMonoidHom
      (TauCeti.QuadraticMap.orthogonalGroupCongr e).injective).symm.trans f⟩

end CFSG.OddStandard.SmallF3.Omega
