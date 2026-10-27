module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Induced

variable {G : Type*} [Group G]

theorem inf_centralizer_eq_map_fixSubgroup {M : Subgroup G} {C : Type*} [Group C]
    (eM : M ≃* C) {t : G} (htM : t ∈ normalizer (M : Set G)) :
    M ⊓ centralizer ({t} : Set G) =
      (fixSubgroup ((eM.symm.trans (M.normalizerMonoidHom ⟨t, htM⟩)).trans eM)).map
        (M.subtype.comp eM.symm.toMonoidHom) := by
  set β : MulAut M := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  ext x
  constructor
  · rintro ⟨hxM, hxt⟩
    refine ⟨eM ⟨x, hxM⟩, ?_, by simp⟩
    change ((eM.symm.trans β).trans eM) (eM ⟨x, hxM⟩) = eM ⟨x, hxM⟩
    rw [F4Pilot.conj_mulEquiv_apply, MulEquiv.symm_apply_apply]
    congr 1
    refine Subtype.ext ?_
    rw [hβ]
    have hxt' := mem_centralizer_singleton_iff.1 hxt
    change t * x * t⁻¹ = x
    calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [hxt']
      _ = x := by group
  · rintro ⟨b, hb, rfl⟩
    have hb' : ((eM.symm.trans β).trans eM) b = b := hb
    rw [F4Pilot.conj_mulEquiv_apply] at hb'
    have hb'' : β (eM.symm b) = eM.symm b := by
      have h1 := congrArg eM.symm hb'
      rwa [MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg Subtype.val hb''
    rw [hβ] at h2
    refine Subgroup.mem_inf.2 ⟨(eM.symm b).2, ?_⟩
    rw [mem_centralizer_singleton_iff]
    change ((eM.symm b : M) : G) * t = t * (eM.symm b : M)
    calc ((eM.symm b : M) : G) * t = t * (eM.symm b : M) * t⁻¹ * t := by rw [h2]
      _ = t * (eM.symm b : M) := by group

theorem normalizerMonoidHom_sq_eq_one_of_orderOf {M : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htM : t ∈ normalizer (M : Set G)) : M.normalizerMonoidHom ⟨t, htM⟩ ^ 2 = 1 := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  refine MulEquiv.ext fun m => Subtype.ext ?_
  rw [sq, MulAut.mul_apply, MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.normalizerMonoidHom_apply_apply_coe]
  calc t * (t * (m : G) * t⁻¹) * t⁻¹ = (t * t) * m * (t * t)⁻¹ := by group
    _ = m := by rw [ht2, one_mul, inv_one, mul_one]

end Induced

end CFSG.SeitzReduction.E6Pilot
