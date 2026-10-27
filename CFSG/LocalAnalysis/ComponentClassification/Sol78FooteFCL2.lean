module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFCB
public import CFSG.Dihedral.Glauberman.DicksonMaxCases

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.ComponentClassification.Foote5 CFSG.ComponentClassification.AutL2Facts
  CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem exists_isKleinFour_psl2 {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (e : Y ≃* PSL2 F) : ∃ V : Subgroup Y, IsKleinFour V := by
  obtain ⟨H, ⟨eH⟩⟩ := Glauberman.Dickson.QuatTable.exists_alternatingFour_subgroup (F := F) h2
  obtain ⟨V, hV4, hVmem⟩ := Glauberman.Dickson.MaxCases.exists_kleinFour eH
  have hVK : IsKleinFour V := FooteLit.isKleinFour_of_card_eq_four hV4 fun x hx => by
    rw [sq]
    exact ((hVmem x).mp hx).2
  exact ⟨V.map e.symm.toMonoidHom, isKleinFour_map_of_injective e.symm.injective hVK⟩

theorem exists_isKleinFour_le_sylow {Y : Type} [Group Y] [Finite Y] {V₀ : Subgroup Y}
    (hV₀ : IsKleinFour V₀) (R : Sylow 2 Y) : ∃ V : Subgroup Y, IsKleinFour V ∧ V ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV₀2 : IsPGroup 2 V₀ := IsPGroup.of_card (n := 2) (by rw [hV₀.card_four]; norm_num)
  obtain ⟨R₀, hR₀⟩ := hV₀2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y R₀ R
  refine ⟨V₀.map (MulAut.conj g).toMonoidHom,
    isKleinFour_map_of_injective (MulAut.conj g).injective hV₀, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have h1 := Subgroup.smul_mem_pointwise_smul v (MulAut.conj g) (R₀ : Subgroup Y) (hR₀ hv)
  rw [← Sylow.coe_subgroup_smul] at h1
  exact hg ▸ h1

theorem fieldCentralizer_a_psl2
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : Blueprint.LieModel Y .PSL 2 p f) {β : MulAut Y} (hβ2 : β * β = 1)
    (hβ : β ∉ innAut5 Y) (hR : ∃ R : Sylow 2 Y, ∀ r ∈ (R : Subgroup Y), β r = r) :
    ∃ X : Subgroup Y, (∀ x ∈ X, β x = x) ∧ Nonempty (X ≃* alternatingGroup (Fin 4)) := by
  classical
  obtain ⟨-, hf, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
  have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 hf hF
  have h2F : (2 : F) ≠ 0 := two_ne_zero_of_card hp hp2 hF
  set x := autEquiv e β with hx
  have hxx : x * x = 1 := by rw [hx, ← map_mul, hβ2, map_one]
  have hxnot : ∀ z : PSL2 F, x ≠ incl F z := fun z hz => by
    apply hβ
    refine ⟨e.symm z, (autEquiv e).injective ?_⟩
    rw [autEquiv_conj, MulEquiv.apply_symm_apply, ← hz]
  by_cases hright : x.right = 1
  ·
    exfalso
    obtain ⟨R, hRfix⟩ := hR
    obtain ⟨V₀, hV₀⟩ := exists_isKleinFour_psl2 h2F e
    obtain ⟨V, hV, hVR⟩ := exists_isKleinFour_le_sylow hV₀ R
    have hxl : x = SemidirectProduct.inl x.left := by
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, hright]
      simp
    set ι : Y →* PGL2 F :=
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp e.toMonoidHom
    have hι : Function.Injective ι :=
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective
    have hc : x.left ∈ centralizer ((V.map ι : Subgroup (PGL2 F)) : Set (PGL2 F)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      have h1 := (apply_eq_iff_commute e β v).mp (hRfix v (hVR hv))
      rw [← hx, hxl, incl_apply, ← map_mul, ← map_mul] at h1
      exact (SemidirectProduct.inl_injective h1).symm
    rw [pgl2_kleinFour_centralizer_eq_self F hodd _ (isKleinFour_map_of_injective hι hV)] at hc
    obtain ⟨v, -, hv⟩ := hc
    apply hxnot (e v)
    rw [hxl, incl_apply, ← hv]
    rfl
  ·
    set σ := x.right with hσdef
    have hσσ : σ * σ = 1 := by
      have h1 := congrArg SemidirectProduct.rightHom hxx
      rwa [map_mul, map_one, SemidirectProduct.rightHom_eq_right] at h1
    have hσ : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hright
    have hx1 : x ≠ 1 := fun h => hright (by rw [hσdef, h]; rfl)
    have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hxx) hx1
    obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd x hxo hright
    obtain ⟨K₀, hK₀, -, -⟩ := exists_fixed_subfield σ hσ
    have h2K : (2 : K₀) ≠ 0 := fun h => h2F (by
      have h1 := congrArg K₀.subtype h
      rwa [map_ofNat, map_zero] at h1)
    obtain ⟨H₀, ⟨eH⟩⟩ :=
      Glauberman.Dickson.QuatTable.exists_alternatingFour_subgroup (F := K₀) h2K
    have hxeq : x = SemidirectProduct.inl C * SemidirectProduct.inr σ *
        (SemidirectProduct.inl C)⁻¹ := by
      rw [← hC]
      group
    set X₂ := (H₀.map (psl2Sub K₀)).map (pglAction F C).toMonoidHom with hX₂
    have hfix : ∀ w ∈ X₂, semilinearAction F x w = w := by
      rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩
      have hz : psl2FieldAut F σ (psl2Sub K₀ z) = psl2Sub K₀ z := psl2Sub_mem_fieldCent hK₀ z
      rw [hxeq, map_mul, map_mul, map_inv, semilinearAction_inl, semilinearAction_inr,
        MulAut.mul_apply, MulAut.mul_apply]
      change pglAction F C (psl2FieldAut F σ ((pglAction F C)⁻¹ (pglAction F C (psl2Sub K₀ z)))) =
        pglAction F C (psl2Sub K₀ z)
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply, hz]
    refine ⟨X₂.map e.symm.toMonoidHom, ?_, ⟨?_⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      apply e.injective
      change e (β (e.symm w)) = e (e.symm w)
      rw [← semilinearAction_autEquiv_apply, ← hx, MulEquiv.apply_symm_apply, hfix w hw]
    · exact (X₂.equivMapOfInjective _ e.symm.injective).symm.trans
        (((H₀.map (psl2Sub K₀)).equivMapOfInjective _ (pglAction F C).injective).symm.trans
          ((H₀.equivMapOfInjective _ (psl2Sub_injective K₀)).symm.trans eH))

end CFSG.ComponentClassification.Sol78
