module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Residual
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_of_sylow_le {S X Y : Subgroup G} (hS : IsSylowTwoOf S X) (hSY : S ≤ Y)
    (hYX : Y ≤ X) : IsSylowTwoOf S Y := by
  refine ⟨hSY, hS.isPGroup, fun hd => hS.2.2 ?_⟩
  have h := Subgroup.relIndex_mul_relIndex S Y X hSY hYX
  exact hd.trans (Dvd.intro _ h)

theorem le_closure_odd_sup_of_isSylowTwoOf {X S : Subgroup G} (hS : IsSylowTwoOf S X) :
    X ≤ Subgroup.closure {x : G | x ∈ X ∧ Odd (orderOf x)} ⊔ S := by
  have hnorm : (pResidual 2 ↥X).Normal := by
    rw [pResidual_two_eq_closure_odd]
    exact normal_closure_odd _
  have hq : IsPGroup 2 (↥X ⧸ pResidual 2 ↥X) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨(orderOf x).factorization 2, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pResidual_two_eq_closure_odd]
    exact Subgroup.subset_closure (odd_orderOf_pow_two_part x)
  have hS2 : IsPGroup 2 (S.subgroupOf X) :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥X := hS2.toSylow hS.2.2
  have htop := CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroup_sup_sylow_eq_top_of_pGroup_quotient
    2 Nat.prime_two (pResidual 2 ↥X) hnorm hq P
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥X) ∈ (P : Subgroup ↥X) ⊔ pResidual 2 ↥X := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem X.subtype hmem
  rw [Subgroup.map_sup] at hmap
  have hP : (P : Subgroup ↥X).map X.subtype = S := by
    rw [show (P : Subgroup ↥X) = S.subgroupOf X from IsPGroup.toSylow_coe _ _]
    exact Subgroup.map_subgroupOf_eq_of_le hS.le
  have hR : (pResidual 2 ↥X).map X.subtype = Subgroup.closure {x : G | x ∈ X ∧ Odd (orderOf x)} :=
    pResidualOf_two_eq_closure_odd X
  rw [hP, hR] at hmap
  rw [sup_comm]
  exact hmap

theorem odd_mem_normalizer_component (he : CFSG.Assembly.evenRank G ≤ 2) {X L : Subgroup G}
    (hX : pCoreOf 2 X ≠ ⊥) (hL : IsComponentIn L X) (hcen : Unc25G2.CentreTwo L) {g : G}
    (hgX : g ∈ X) (hodd : Odd (orderOf g)) : g ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hgn
  have hgg : g * g ∈ X := X.mul_mem hgX hgX
  have hL₂ : IsComponentIn (CFSG.conjugate L g) X := Unc25G2.isComponentIn_conjugate hL hgX
  have hL₃ : IsComponentIn (CFSG.conjugate L (g * g)) X :=
    Unc25G2.isComponentIn_conjugate hL hgg
  have h12 : CFSG.conjugate L g ≠ L := fun h =>
    hgn (BenderBranch.conjugate_eq_iff_mem_normalizer.mp h)
  have h13 : CFSG.conjugate L (g * g) ≠ L := by
    intro h
    apply hgn
    have hggN : g * g ∈ Subgroup.normalizer (L : Set G) :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mp h
    obtain ⟨m, hm⟩ := hodd
    have h1 : g ^ (2 * m + 1) = 1 := by
      rw [← hm]
      exact pow_orderOf_eq_one g
    have hg : g = (g * g) ^ (m + 1) := by
      calc g = g ^ (2 * m + 1) * g := by rw [h1, one_mul]
        _ = g ^ (2 * m + 2) := by rw [← pow_succ]
        _ = (g * g) ^ (m + 1) := by rw [← sq, ← pow_mul]; ring_nf
    rw [hg]
    exact (Subgroup.normalizer (L : Set G)).pow_mem hggN _
  have h23 : CFSG.conjugate L (g * g) ≠ CFSG.conjugate L g := by
    intro h
    apply h12
    have := congrArg (fun Y => CFSG.conjugate Y g⁻¹) h
    simpa only [BenderBranch.conjugate_conjugate, mul_inv_cancel_right, mul_inv_cancel,
      BenderBranch.conjugate_one] using this
  have c12 : ⁅L, CFSG.conjugate L g⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hL hL₂).resolve_left fun h => h12 h.symm
  have c13 : ⁅L, CFSG.conjugate L (g * g)⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hL hL₃).resolve_left fun h => h13 h.symm
  have c23 : ⁅CFSG.conjugate L g, CFSG.conjugate L (g * g)⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hL₂ hL₃).resolve_left fun h => h23 h.symm
  obtain ⟨p, hp, hp2, hpd⟩ := Unc25G2.exists_odd_prime_dvd_card hL
  have hd₂ : p ∣ Nat.card (CFSG.conjugate L g) := by rwa [BenderBranch.card_conjugate]
  have hd₃ : p ∣ Nat.card (CFSG.conjugate L (g * g)) := by
    rwa [BenderBranch.card_conjugate]
  have hZ₁ : ∀ x ∈ L, (∀ y ∈ L, y * x = x * y) → x ^ p = 1 → x = 1 := by
    intro x hx hxc hxp
    obtain ⟨k, hk⟩ := hcen x hx hxc
    exact Unc25G2.eq_one_of_pow_eq_one_of_two_pow hp hp2 hxp hk
  have hZ₂ : ∀ x ∈ CFSG.conjugate L g, (∀ y ∈ CFSG.conjugate L g, y * x = x * y) → x ^ p = 1 →
      x = 1 := by
    intro x hx hxc hxp
    obtain ⟨k, hk⟩ := (hcen.conjugate g) x hx hxc
    exact Unc25G2.eq_one_of_pow_eq_one_of_two_pow hp hp2 hxp hk
  obtain ⟨E, hEle, hE, hEcard⟩ := Unc25G2.exists_elemAbelian_card_cube_of_commuting hp c12 c13
    c23 hZ₁ hZ₂ hpd hd₂ hd₃
  have hEX : E ≤ X := hEle.trans (sup_le (sup_le hL.1 hL₂.1) hL₃.1)
  exact Unc25G2.false_of_isElemAbelian_card_cube he hX hEX hp hp2 hE hEcard

theorem inf_oddCoreIn_eq_bot_of_simple {X L : Subgroup G} (hLX : L ≤ X) (hsimple : IsSimpleGroup ↥L)
    (heven : 2 ∣ Nat.card L) : L ⊓ oddCoreIn X = ⊥ := by
  have hn : ((L ⊓ oddCoreIn X).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro a l ha hl
    refine ⟨L.mul_mem (L.mul_mem hl ha.1) (L.inv_mem hl), ?_⟩
    have hlX : l ∈ Subgroup.normalizer (oddCoreIn X : Set G) :=
      le_normalizer_oddCoreIn X (hLX hl)
    exact (Subgroup.mem_normalizer_iff.mp hlX a).mp ha.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ oddCoreIn X).subgroupOf L) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ L := hx.1
    have : (⟨x, hxL⟩ : ↥L) ∈ (L ⊓ oddCoreIn X).subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hLle : L ≤ oddCoreIn X := by
      intro x hx
      have : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ oddCoreIn X).subgroupOf L := by rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    have hdvd : Nat.card L ∣ Nat.card (oddCoreIn X) := Subgroup.card_dvd_of_le hLle
    exact (odd_card_oddCoreIn X).not_two_dvd_nat (heven.trans hdvd)

end General

end CFSG.QuasithinUnique
