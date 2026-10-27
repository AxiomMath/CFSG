module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Gen
public import CFSG.Sporadic.SuzOddCore.CTIComponents

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC.ResidualA8

open CFSG CFSG.LocalCores CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Sporadic.SuzOddCore

section Suz


theorem suzD_not_equiv_alt_eight : ¬ Nonempty (suzD ≃* alternatingGroup (Fin 8)) :=
  not_equiv_alt_eight_of_classes classEquiv (fun l => classSizes.getD l 0) card_class 0
    classEquiv_zero (by
      intro l hl
      rw [card_suzD]
      revert l
      decide)

theorem noAltEightComponent_invE_zero : NoAltEightComponent (invE 0) := by
  set ρ' : invE 0 →* rho0.range := rho0.rangeRestrict
  have hsurj : Function.Surjective ρ' := MonoidHom.rangeRestrict_surjective rho0
  have hker : Group.IsSolvable ρ'.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have hp : IsPGroup 2 rho0.ker := IsPGroup.of_card (n := 2) (by rw [card_ker_rho0]; norm_num)
    have : Group.IsNilpotent rho0.ker := hp.isNilpotent
    infer_instance
  have e : suzD.subgroupOf rho0.range ≃* suzD := Subgroup.subgroupOfEquivOfLe suzD_le
  have hs : IsSimpleGroup (suzD.subgroupOf rho0.range) := by
    have := suzD_simple
    exact e.isSimpleGroup
  have hnc : ∃ a b : suzD.subgroupOf rho0.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := suzD_noncomm
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  refine NoAltEightComponent.of_surjective_simple ρ' hsurj hker (suzD.subgroupOf rho0.range)
    suzD_index hs hnc ?_
  rintro ⟨φ⟩
  exact suzD_not_equiv_alt_eight ⟨e.symm.trans φ⟩

theorem noAltEightComponent_invE_one : NoAltEightComponent (invE 1) :=
  NoAltEightComponent.of_no_component CTI_Suz_second_involution_centralizer_has_no_components.2

theorem noAltEightComponent_suz_centralizer {S : Type*} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Suz) (a : S) (ha : orderOf a = 2) :
    NoAltEightComponent (Subgroup.centralizer ({a} : Set S)) := by
  set f : S ≃* suzM := e.trans suzEquivM
  set a' : Equiv.Perm (Fin 1782) := ((f a : suzM) : Equiv.Perm (Fin 1782))
  have ha' : orderOf a' = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha]
  have hinj : Function.Injective (suzM.subtype.comp f.toMonoidHom) :=
    suzM.subtype_injective.comp f.injective
  have g1 : Subgroup.centralizer ({a} : Set S) ≃*
      (suzM ⊓ Subgroup.centralizer {a'} : Subgroup (Equiv.Perm (Fin 1782))) :=
    ((Subgroup.centralizer ({a} : Set S)).equivMapOfInjective _ hinj).trans
      (MulEquiv.subgroupCongr (centralizer_map_equiv f a))
  obtain ⟨c, hc, h01⟩ := suzM_involution_class (f a).2 ha'
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
    exact NoAltEightComponent.of_mulEquiv (g1.trans g2) noAltEightComponent_invE_zero
  · obtain ⟨g2⟩ := key 1 (by norm_num) h1
    exact NoAltEightComponent.of_mulEquiv (g1.trans g2) noAltEightComponent_invE_one

end Suz

end CFSG.ComponentClassification.CatFC.ResidualA8
