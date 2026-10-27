module

public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.B.Co2Catalog
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.B.Short

theorem Kstab_rStar_simple :
    IsSimpleGroup (Kstab (phi0 (coordOf rStar))) ∧
      Nat.card (Kstab (phi0 (coordOf rStar))) = 42305421312000 := by
  have h := (Co2.native_short_stabilizer_simple.1 (vMinus 0 1) (vMinus_mem (by decide))).2.2
  have hs := (Co2.native_short_stabilizer_simple.1 (vMinus 0 1) (vMinus_mem (by decide))).1
  have e : Kstab (classOf (vMinus 0 1)) ≃* Kstab (phi0 (coordOf rStar)) :=
    MulEquiv.subgroupCongr (congrArg Kstab phi0_coordOf_rStar.symm)
  exact ⟨@MulEquiv.isSimpleGroup _ _ _ _ hs e.symm, (Nat.card_congr e.toEquiv).symm.trans h⟩

theorem pCore_Jbar : CFSG.pCore 2 Jbar = Ebar.subgroupOf Jbar := by
  have hEcard : Nat.card (Ebar.subgroupOf Jbar) = 2 ^ 23 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar).toEquiv).trans
      Ebar_extraspecial.2
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, IsPGroup.of_card hEcard⟩)
  obtain ⟨hsimple, hcard⟩ := Kstab_rStar_simple
  have := hsimple
  have : Finite (Kstab (phi0 (coordOf rStar))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hn : ((CFSG.pCore 2 Jbar).map jbarToKv).Normal :=
    Subgroup.Normal.map pCore_normal jbarToKv jbarToKv_surjective
  have hp : IsPGroup 2 ((CFSG.pCore 2 Jbar).map jbarToKv) := IsPGroup.map pCore_isPGroup _
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · rw [← ker_jbarToKv, ← Subgroup.map_eq_bot_iff]
    exact hbot
  · exfalso
    rw [htop] at hp
    have hp' : IsPGroup 2 (Kstab (phi0 (coordOf rStar))) := hp.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn'⟩ := (IsPGroup.iff_card (p := 2)).1 hp'
    rw [hcard] at hn'
    have h3 : 3 ∣ 2 ^ n := by rw [← hn']; norm_num
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) (by norm_num)).1
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)
    omega

theorem centralizer_Ebar_eq : Subgroup.centralizer (Ebar : Set Cbar) = Subgroup.zpowers xbar := by
  apply le_antisymm
  · intro c hc
    have hcx : c ∈ Subgroup.centralizer ({xbar} : Set Cbar) :=
      Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hc) xbar xbar_mem_Ebar).symm
    rw [centralizer_xbar] at hcx
    rw [← centralizer_Ebar]
    exact ⟨hcx, hc⟩
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro e he
    have hx : xbar ∈ (Subgroup.center Ebar).map Ebar.subtype := by
      rw [map_center_Ebar]
      exact Subgroup.mem_zpowers xbar
    obtain ⟨z, hz, hzx⟩ := hx
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨e, he⟩)
    rw [← hzx]
    change e * (z : Cbar) = (z : Cbar) * e
    simpa using h

theorem zQ_mul_wQ_mem_centralizer : zQ * wQ ∈ Subgroup.centralizer {rStar} := by
  have hspin := triality_four_group_spin_identification
  have hy : xmatTau = rhoEquiv (zQ * wQ) := hspin.2.2.2.2.2.1
  have hc := commute_tStar_of_mem_Cgen xmatTau_mem_Cgen
  rw [hy, tStar, ← rhoEquiv_mul, ← rhoEquiv_mul] at hc
  exact Subgroup.mem_centralizer_singleton_iff.2 (rhoEquiv_injective hc).symm

theorem conj_xbar_mem_Ebar : taubar * xbar * taubar⁻¹ ∈ Ebar := by
  rw [taubar_conj_xbar]
  have e : yC = ⟨rhoEquiv (zQ * wQ), rhoEquiv_mem_Cgen zQ_mul_wQ_mem_centralizer⟩ :=
    Subtype.ext triality_four_group_spin_identification.2.2.2.2.2.1
  change kappa yC ∈ Ebar
  rw [e]
  exact kappa_rho_mem_Ebar zQ_mul_wQ_mem_centralizer

theorem conj_xbar_not_mem_zpowers : taubar * xbar * taubar⁻¹ ∉ Subgroup.zpowers xbar := by
  rw [taubar_conj_xbar, Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbar]
  rintro (h | h)
  · exact ybar_ne_one h
  · exact xbar_ne_ybar h.symm

theorem exists_mul_ne_mul_Cbar : ∃ a b : Cbar, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have htop : Subgroup.center Ebar = ⊤ := by
    rw [eq_top_iff]
    intro e _
    rw [Subgroup.mem_center_iff]
    intro f
    exact Subtype.ext (h f e)
  have hc := Ebar_extraspecial.1.2.2.2
  rw [htop, Subgroup.card_top, Ebar_extraspecial.2] at hc
  norm_num at hc

theorem exists_surjective_ker_eq_of_quotient_equiv {J : Type*} [Group J] (N : Subgroup J)
    [N.Normal] {G : Type*} [Group G] (e : J ⧸ N ≃* G) :
    ∃ f : J →* G, Function.Surjective f ∧ f.ker = N := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' N),
    e.surjective.comp (QuotientGroup.mk'_surjective N), ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem jbar_exact_sequence : ∃ f : Jbar →* Blueprint.NativeSporadic.Co2,
    Function.Surjective f ∧ f.ker = Ebar.subgroupOf Jbar :=
  exists_surjective_ker_eq_of_quotient_equiv _ Co2Catalog.jbarQuotEquiv

theorem short_centralizer_Co2_local_recognition_hypotheses :
    Finite Cbar ∧ IsSimpleGroup Cbar ∧ (∃ a b : Cbar, a * b ≠ b * a) ∧
      Subgroup.centralizer {xbar} = Jbar ∧ CFSG.pCore 2 Jbar = Ebar.subgroupOf Jbar ∧
      IsExtraspecialPGroup 2 Ebar ∧ Nat.card Ebar = 2 ^ 23 ∧
      (Subgroup.center Ebar).map Ebar.subtype = Subgroup.zpowers xbar ∧
      (∃ f : Jbar →* Blueprint.NativeSporadic.Co2,
        Function.Surjective f ∧ f.ker = Ebar.subgroupOf Jbar) ∧
      Subgroup.centralizer (Ebar : Set Cbar) = Subgroup.zpowers xbar ∧
      taubar * xbar * taubar⁻¹ ∈ Ebar ∧ taubar * xbar * taubar⁻¹ ∉ Subgroup.zpowers xbar ∧
      {y | ∃ c : Cbar, c * xbar * c⁻¹ = y} ∩
        ((CFSG.pCore 2 Jbar).map Jbar.subtype : Set Cbar) ≠ {xbar} := by
  obtain ⟨hfin, -, hsimple, -⟩ := short_centralizer_generated_quotient_simple
  refine ⟨hfin, hsimple, exists_mul_ne_mul_Cbar, centralizer_xbar, pCore_Jbar,
    Ebar_extraspecial.1, Ebar_extraspecial.2, map_center_Ebar, ?_, centralizer_Ebar_eq,
    conj_xbar_mem_Ebar, conj_xbar_not_mem_zpowers, ?_⟩
  · exact jbar_exact_sequence
  · intro h
    have hmem : taubar * xbar * taubar⁻¹ ∈ {y | ∃ c : Cbar, c * xbar * c⁻¹ = y} ∩
        ((CFSG.pCore 2 Jbar).map Jbar.subtype : Set Cbar) := by
      refine ⟨⟨taubar, rfl⟩, ?_⟩
      rw [pCore_Jbar]
      exact ⟨⟨_, Ebar_le_Jbar conj_xbar_mem_Ebar⟩, conj_xbar_mem_Ebar, rfl⟩
    have hx : taubar * xbar * taubar⁻¹ = xbar :=
      Set.mem_singleton_iff.1 ((Set.ext_iff.1 h _).1 hmem)
    apply conj_xbar_not_mem_zpowers
    rw [hx]
    exact Subgroup.mem_zpowers xbar

end CFSG.ComponentClassification.BMCase
