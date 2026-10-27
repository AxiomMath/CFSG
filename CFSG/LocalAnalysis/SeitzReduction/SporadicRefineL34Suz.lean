module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSuz
public import CFSG.Sporadic.SuzOddCore.CTIComponents

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

section Suz


theorem suz_inner_fixedSubgroup_cases {S : Type} [Group S] (e : S ≃* NativeSporadic.Suz) (s : S)
    (hs : orderOf s = 2) :
    Nonempty (fixedSubgroup (MulAut.conj s) ≃* invE 0) ∨
      Nonempty (fixedSubgroup (MulAut.conj s) ≃* invE 1) := by
  set f : S ≃* suzM := e.trans suzEquivM
  set a' : Equiv.Perm (Fin 1782) := ((f s : suzM) : Equiv.Perm (Fin 1782))
  have ha' : orderOf a' = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hs]
  have hinj : Function.Injective (suzM.subtype.comp f.toMonoidHom) :=
    suzM.subtype_injective.comp f.injective
  let g1 : fixedSubgroup (MulAut.conj s) ≃*
      (suzM ⊓ Subgroup.centralizer {a'} : Subgroup (Equiv.Perm (Fin 1782))) :=
    (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)).trans
      (((Subgroup.centralizer ({s} : Set S)).equivMapOfInjective _ hinj).trans
      (MulEquiv.subgroupCongr (centralizer_map_equiv f s)))
  obtain ⟨c, hc, h01⟩ := suzM_involution_class (f s).2 ha'
  have key : ∀ i < 4, c * suzInv i * c⁻¹ = a' →
      Nonempty ((suzM ⊓ Subgroup.centralizer {a'} : Subgroup (Equiv.Perm (Fin 1782))) ≃*
        invE i) := by
    intro i hi hca
    have hmap := map_conj_inf_centralizer (Γ := suzM) (c := c) (suzM_conj_iff hc) (suzInv i)
    rw [hca] at hmap
    have e2 := (Subgroup.equivMapOfInjective (suzM ⊓ Subgroup.centralizer {suzInv i})
      (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap)
    have e3 : invE i = suzM ⊓ Subgroup.centralizer {suzInv i} := by
      rw [invE_eq_centM hi, centM, inf_comm]
    exact ⟨e2.symm.trans (MulEquiv.subgroupCongr e3.symm)⟩
  rcases h01 with h0 | h1
  · obtain ⟨g2⟩ := key 0 (by norm_num) h0
    exact .inl ⟨g1.trans g2⟩
  · obtain ⟨g2⟩ := key 1 (by norm_num) h1
    exact .inr ⟨g1.trans g2⟩

theorem suz_inner_not_twoSmall {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Suz)
    {s : S} (hs : orderOf s = 2) {D : Subgroup (fixedSubgroup (MulAut.conj s))}
    (hD : IsComponent D) : ¬ FixedCentralizerTwoSmall (MulAut.conj s) D := by
  rcases suz_inner_fixedSubgroup_cases e s hs with h0 | h1
  · obtain ⟨φ⟩ := h0
    exact not_fixedCentralizerTwoSmall_of_mulEquiv_ker hD φ rho0 card_ker_rho0
  · obtain ⟨φ⟩ := h1
    exact (CTI_Suz_second_involution_centralizer_has_no_components.2 _
      (LocalCores.isComponent_map_mulEquiv φ hD)).elim

theorem suz_l34_outer_card {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Suz) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 20160)
    (hσD : (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
      FixedCentralizerTwoFree σ D) :
    σ ∉ (MulAut.conj : S →* MulAut S).range ∧ Nat.card (fixedSubgroup σ) = 1209600 := by
  have := hS
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · exfalso
    obtain ⟨s, rfl⟩ := hin
    have hs : orderOf s = 2 := by
      rw [← orderOf_injective _
        (ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna) s]
      exact hσ
    rcases hσD with ⟨-, hsmall⟩ | hfree
    · exact suz_inner_not_twoSmall e hs hD hsmall
    · exact LinearPilot.not_mem_range_conj_of_twoFree hna hσ hfree ⟨s, rfl⟩
  · refine ⟨hin, ?_⟩
    have h := card_quotient_center_dvd_card_fixedSubgroup D
    rcases suz_outer_card_fixedSubgroup e hσ hin with h1 | h1
    · rw [hcard, h1] at h
      norm_num at h
    · exact h1

end Suz

end CFSG.SeitzReduction.SporadicRefine
