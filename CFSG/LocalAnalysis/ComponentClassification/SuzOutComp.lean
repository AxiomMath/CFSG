module

public import CFSG.LocalAnalysis.ComponentClassification.SuzOutCompT3
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpInputs
public import CFSG.RankThree.PartOne.KS.Suz
public import CFSG.Sporadic.SuzOddCore.CTIComponents

public noncomputable section

namespace CFSG.ComponentClassification.SolMax

open CFSG CFSG.LocalCores Subgroup CFSG.Sporadic.SuzOddCore CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

theorem suzOuterComponentsInput_holds :
    SuzOuterComponentsInput := by
  intro G _ ⟨e⟩ α hα hout B hB
  set f : G ≃* suzM := e.trans suzEquivM with hf
  set α' : MulAut suzM := MulAut.congr f α with hα'
  have hA := CFSG.RankThree.PartOne.suz_autModel
  set x : Equiv.Perm (Fin 1782) := hA.elt α' with hx
  have hxT : x ∈ suzT := hA.elt_mem α'
  have hxspec : ∀ p : suzM, ((α' p : suzM) : Equiv.Perm (Fin 1782)) = x * p * x⁻¹ :=
    hA.elt_spec α'
  have hxM : x ∉ suzM := by
    intro hxM
    apply hout
    refine ⟨f.symm ⟨x, hxM⟩, (MulAut.congr f).injective ?_⟩
    rw [congr_conj f, MulEquiv.apply_symm_apply]
    refine MulEquiv.ext fun q => Subtype.ext ?_
    rw [← hα', hxspec q]
    simp [MulAut.conj_apply]
  have hx2 : orderOf x = 2 := by
    have h1 : α' * α' = 1 := by rw [hα', ← map_mul, hα, map_one]
    have h2 : hA.hom α' * hA.hom α' = 1 := by rw [← map_mul, h1, map_one]
    rw [CFSG.Sporadic.SmallOddCore.AutModel.hom_apply] at h2
    have hx1 : x ≠ 1 := fun h => hxM (h ▸ suzM.one_mem)
    exact orderOf_eq_prime (by rw [pow_two]; exact h2) hx1
  obtain ⟨i, ⟨hi, c, hc, hcx⟩, -⟩ := suzT_involution_class hxT hx2
  have htM : suzInv i ∉ suzM := fun h => hxM (hcx ▸ suzT_conj_mem_suzM hc h)
  obtain ⟨-, h0, h1, -⟩ := invT_check
  have hi23 : i = 2 ∨ i = 3 := by
    interval_cases i
    · exact absurd ((suzInv_mem_iff_inM (by norm_num)).2 h0) htM
    · exact absurd ((suzInv_mem_iff_inM (by norm_num)).2 h1) htM
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hmap1 : (fixSub α).map (suzM.subtype.comp f.toMonoidHom) =
      suzM ⊓ centralizer {x} := by
    ext y
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MonoidHom.comp_apply,
      Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : α g = g := hg
      have h2 := hxspec (f g)
      have h3 : α' (f g) = f g := by
        rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply, hg']
      rw [h3] at h2
      refine ⟨(f g).2, ?_⟩
      calc ((f g : suzM) : Equiv.Perm (Fin 1782)) * x
          = x * (f g : Equiv.Perm (Fin 1782)) * x⁻¹ * x := by rw [← h2]
        _ = x * (f g : Equiv.Perm (Fin 1782)) := by group
    · rintro ⟨hyM, hyc⟩
      refine ⟨f.symm ⟨y, hyM⟩, ?_, by simp⟩
      show α (f.symm ⟨y, hyM⟩) = f.symm ⟨y, hyM⟩
      apply f.injective
      have h2 : α' ⟨y, hyM⟩ = ⟨y, hyM⟩ := by
        refine Subtype.ext ?_
        rw [hxspec]
        calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hyc]
          _ = y := by group
      rw [hα', MulAut.congr_apply] at h2
      simpa using h2
  have g1 : fixSub α ≃* ↥(suzM ⊓ centralizer {x} : Subgroup (Equiv.Perm (Fin 1782))) :=
    ((fixSub α).equivMapOfInjective _ (suzM.subtype_injective.comp f.injective)).trans
      (MulEquiv.subgroupCongr hmap1)
  have hmap2 := map_conj_inf_centralizer (Γ := suzM) (c := c) (suzM_conj_iff hc) (suzInv i)
  rw [hcx] at hmap2
  have g2 := (Subgroup.equivMapOfInjective (suzM ⊓ centralizer {suzInv i})
    (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap2)
  have g3 : invE i = suzM ⊓ centralizer {suzInv i} := by
    rw [invE_eq_centM hi, centM, inf_comm]
  obtain ⟨hB', hcard⟩ :=
    component_quotient_of_equiv (g1.trans (g2.symm.trans (MulEquiv.subgroupCongr g3.symm))) hB
  rw [hcard]
  rcases hi23 with rfl | rfl
  · exact Or.inl (SuzOutComp.invE2_components hB')
  · exact Or.inr (SuzOutComp.invE3_components hB')

end CFSG.ComponentClassification.SolMax
