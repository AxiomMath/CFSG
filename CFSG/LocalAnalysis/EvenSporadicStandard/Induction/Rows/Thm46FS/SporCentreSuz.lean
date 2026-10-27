module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Suz

public noncomputable section

namespace CFSG.EvenSporadicStandard.Induction.SporCentre

open CFSG CFSG.LocalCores Subgroup CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.GSThmB.CF23L34

section Suz


theorem eq_one_of_mem_suzL_of_rho0_eq_one {x : ↥(invE 0)}
    (hx : x ∈ suzL.subgroupOf (invE 0)) (h : rho0 x = 1) : x = 1 := by
  have hLE : suzL ≤ invE 0 := by
    rw [invE_eq_centM (by norm_num)]
    exact suzL_le_centM
  set L₀ := suzL.subgroupOf (invE 0) with hL₀
  have hk4 := card_ker_rho0
  have hcL : Nat.card L₀ = 20160 := by
    rw [hL₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLE).toEquiv, card_suzL]
  have hsL : IsSimpleGroup ↥L₀ := by
    have := isSimpleGroup_suzL
    exact (Subgroup.subgroupOfEquivOfLe hLE).isSimpleGroup
  set ρL := rho0.comp L₀.subtype with hρL
  have hinj : Function.Injective ρL := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρL.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).1 h
    · exfalso
      have hle : L₀ ≤ rho0.ker := fun l hl => by
        have : (⟨l, hl⟩ : ↥L₀) ∈ ρL.ker := h ▸ mem_top _
        exact this
      have := Subgroup.card_le_of_le hle
      rw [hcL, hk4] at this
      omega
  exact congrArg Subtype.val (hinj (a₁ := ⟨x, hx⟩) (a₂ := 1) (by simpa [hρL] using h))

theorem center_eq_bot_of_component_E₀ {B : Subgroup ↥(invE 0)} (hB : IsComponent B) :
    center B = ⊥ := by
  have hk4 := card_ker_rho0
  have hker : Group.IsSolvable rho0.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have hp : IsPGroup 2 rho0.ker := IsPGroup.of_card (n := 2) (by rw [hk4]; norm_num)
    have : Group.IsNilpotent rho0.ker := hp.isNilpotent
    infer_instance
  have hNab : ∀ x ∈ rho0.rangeRestrict.ker, ∀ y ∈ rho0.rangeRestrict.ker, x * y = y * x := by
    intro x hx y hy
    rw [MonoidHom.ker_rangeRestrict] at hx hy
    have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := rho0.ker)
      (by rw [hk4]; norm_num)
    exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have e : suzD.subgroupOf rho0.range ≃* suzD := Subgroup.subgroupOfEquivOfLe suzD_le
  have hs : IsSimpleGroup (suzD.subgroupOf rho0.range) := by
    have := suzD_simple
    exact e.isSimpleGroup
  have hnc : ∃ a b : suzD.subgroupOf rho0.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := suzD_noncomm
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  refine center_eq_bot_of_le rho0.rangeRestrict (MonoidHom.rangeRestrict_surjective rho0) hker
    suzD_index hs hnc hB (component_le_suzL hB) ?_
  rw [eq_bot_iff]
  intro x hx
  rw [mem_inf, MonoidHom.mem_ker] at hx
  rw [mem_bot]
  exact eq_one_of_mem_suzL_of_rho0_eq_one hx.1 (Subtype.ext_iff.1 hx.2)

end Suz

theorem center_eq_bot_of_component_suz
    {S : Type*} [Group S] (e : S ≃* Blueprint.NativeSporadic.Suz) {a : S} (ha : orderOf a = 2)
    {Q : Subgroup S} (hQC : Q ≤ centralizer ({a} : Set S))
    (hQ : IsComponent (Q.subgroupOf (centralizer ({a} : Set S)))) : center Q = ⊥ := by
  set f : S ≃* suzM := e.trans suzEquivM
  set a' : Equiv.Perm (Fin 1782) := ((f a : suzM) : Equiv.Perm (Fin 1782))
  have ha' : orderOf a' = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha]
  have g1 := centralizerEquivInf suzM f a
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
    exact center_eq_bot_of_component_equiv (g1.trans g2)
      (fun B hB => center_eq_bot_of_component_E₀ hB) hQC hQ
  · exfalso
    obtain ⟨g2⟩ := key 1 (by norm_num) h1
    exact CTI_Suz_second_involution_centralizer_has_no_components.2 _
      (isComponent_map_mulEquiv (g1.trans g2) hQ)

end CFSG.EvenSporadicStandard.Induction.SporCentre
