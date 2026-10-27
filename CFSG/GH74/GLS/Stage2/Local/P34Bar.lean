module

public import CFSG.GH74.GLS.Stage2.Local.P34Embed
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

variable {G : Type} [Group G] [Finite G]

section Basic

variable (H : Subgroup G)

abbrev mkH : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H)

omit [Finite G] in
theorem odd_orderOf_of_mem_pPrimeCore {X : Type} [Group X] [Finite X] {o : X}
    (ho : o ∈ pPrimeCore 2 X) : Odd (orderOf o) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf o ∣ Nat.card ↥(pPrimeCore 2 X) := by
    have := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 X) ho
    simpa using this
  exact Odd.of_dvd_nat (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := X))) h1

theorem odd_card_pPrimeCore : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.odd_iff.2 (by
    have := (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥H)))
    exact Nat.odd_iff.1 this)

theorem odd_orderOf_of_mem_core {o : ↥H} (ho : o ∈ pPrimeCore 2 ↥H) : Odd (orderOf o) := by
  have h1 : orderOf o ∣ Nat.card ↥(pPrimeCore 2 ↥H) := by
    have := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥H) ho
    simpa using this
  exact Odd.of_dvd_nat (odd_card_pPrimeCore H) h1

omit [Finite G] in
theorem mkH_eq_one_iff {h : ↥H} : mkH H h = 1 ↔ h ∈ pPrimeCore 2 ↥H :=
  QuotientGroup.eq_one_iff h

theorem orderOf_mk_eq_two {t : ↥H} (ht : orderOf t = 2) : orderOf (mkH H t) = 2 := by
  have h2 : (mkH H t) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    rw [← map_pow, h, map_one]
  have h1 : mkH H t ≠ 1 := by
    intro h
    have := odd_orderOf_of_mem_core H ((mkH_eq_one_iff H).1 h)
    rw [ht] at this
    exact absurd this (by decide)
  exact orderOf_eq_prime h2 h1

theorem exists_lift_involution {u : HBar H} (hu : orderOf u = 2) :
    ∃ t : ↥H, orderOf t = 2 ∧ mkH H t = u := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H) u
  have hn : orderOf h ≠ 0 := (orderOf_pos h).ne'
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  have hdvd : m ∣ orderOf h := ⟨2 ^ a, by rw [hord]; ring⟩
  have ht : orderOf (h ^ m) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hm0 hdvd, hord]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hu2 : (mkH H h) ^ 2 = 1 := by
    have h' := pow_orderOf_eq_one (mkH H h)
    rw [hu] at h'
    exact h'
  have hmk : mkH H (h ^ m) = mkH H h := by
    obtain ⟨k, hk⟩ := hm
    rw [map_pow, hk, pow_succ, pow_mul, hu2, one_pow, one_mul]
  have hu1 : mkH H h ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu
    omega
  refine ⟨h ^ m, ?_, hmk⟩
  have ht2 : (h ^ m) ^ 2 ∈ pPrimeCore 2 ↥H := by
    rw [← mkH_eq_one_iff, map_pow, hmk, hu2]
  have hodd := odd_orderOf_of_mem_core H ht2
  have hd1 : orderOf ((h ^ m) ^ 2) ∣ 2 ^ a := ht ▸ orderOf_pow_dvd 2
  have hcop : Nat.Coprime (orderOf ((h ^ m) ^ 2)) (2 ^ a) :=
    (Nat.coprime_two_right.2 hodd).pow_right a
  have hone : orderOf ((h ^ m) ^ 2) = 1 := Nat.Coprime.eq_one_of_dvd hcop hd1
  have hsq : (h ^ m) ^ 2 = 1 := orderOf_eq_one_iff.1 hone
  have hne : h ^ m ≠ 1 := by
    intro h1
    apply hu1
    rw [← hmk, h1, map_one]
  exact orderOf_eq_prime hsq hne

theorem exists_mem_core_conj {z u : ↥H} (hz : orderOf z = 2) (hu : orderOf u = 2)
    (h : mkH H u = mkH H z) : ∃ p ∈ pPrimeCore 2 ↥H, u = p⁻¹ * z * p := by
  have hzz : z * z = 1 := by
    have h' := pow_orderOf_eq_one z
    rw [hz] at h'
    simpa [pow_two] using h'
  have huu : u * u = 1 := by
    have h' := pow_orderOf_eq_one u
    rw [hu] at h'
    simpa [pow_two] using h'
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  set o : ↥H := z⁻¹ * u with ho
  have hoO : o ∈ pPrimeCore 2 ↥H := by
    rw [← mkH_eq_one_iff, ho, map_mul, map_inv, h]
    simp
  have hzo : z * o * z⁻¹ = o⁻¹ := by
    rw [ho, hzi, mul_inv_rev, hui, hzi]
    calc z * (z * u) * z = (z * z) * u * z := by group
      _ = u * z := by rw [hzz, one_mul]
  have hodd := odd_orderOf_of_mem_core H hoO
  obtain ⟨j, hj⟩ := hodd
  set p : ↥H := o ^ (j + 1) with hp
  have hpO : p ∈ pPrimeCore 2 ↥H := Subgroup.pow_mem _ hoO _
  have hpp : p * p = o := by
    rw [hp, ← pow_add, show j + 1 + (j + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hzp : z * p * z⁻¹ = p⁻¹ := by
    rw [hp, ← conj_pow, hzo, inv_pow]
  refine ⟨p, hpO, ?_⟩
  have hzp' : z * p = p⁻¹ * z := (mul_inv_eq_iff_eq_mul.1 hzp)
  have hzo' : z * o = o⁻¹ * z := (mul_inv_eq_iff_eq_mul.1 hzo)
  have hzou : z * o = u := by rw [ho]; group
  calc u = z * o := hzou.symm
    _ = o⁻¹ * z := hzo'
    _ = (p * p)⁻¹ * z := by rw [hpp]
    _ = p⁻¹ * (p⁻¹ * z) := by group
    _ = p⁻¹ * (z * p) := by rw [hzp']
    _ = p⁻¹ * z * p := by group

omit [Finite G] in
theorem mk_isConj_of_isConj {t z : ↥H} (h : IsConj t z) : IsConj (mkH H t) (mkH H z) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨mkH H c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩

theorem isConj_of_mk_isConj {t z : ↥H} (ht : orderOf t = 2) (hz : orderOf z = 2)
    (h : IsConj (mkH H t) (mkH H z)) : IsConj t z := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H) c
  have hu : orderOf (g * t * g⁻¹) = 2 :=
    (orderOf_eq_of_isConj' (isConj_iff.2 ⟨g, rfl⟩)).symm.trans ht
  obtain ⟨p, hp, hpu⟩ := exists_mem_core_conj H hz hu (by rw [map_mul, map_mul, map_inv]; exact hc)
  refine isConj_iff.2 ⟨p * g, ?_⟩
  calc p * g * t * (p * g)⁻¹ = p * (g * t * g⁻¹) * p⁻¹ := by group
    _ = p * (p⁻¹ * z * p) * p⁻¹ := by rw [← hpu]
    _ = z := by group

end Basic

section Cen

variable (H : Subgroup G) {z : G}

theorem centralizer_mk_eq (hz : orderOf z = 2) (hzH : z ∈ H) :
    centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) = barIn H (Cen z) := by
  have hzH' : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by
    rw [← hz]
    exact (Subgroup.orderOf_coe (⟨z, hzH⟩ : ↥H)).symm
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H) y
    have hu : orderOf (h * ⟨z, hzH⟩ * h⁻¹) = 2 :=
      (orderOf_eq_of_isConj' (isConj_iff.2 ⟨h, rfl⟩)).symm.trans hzH'
    have hmk : mkH H (h * ⟨z, hzH⟩ * h⁻¹) = mkH H ⟨z, hzH⟩ := by
      rw [map_mul, map_mul, map_inv, hy]
      group
    obtain ⟨p, hp, hpu⟩ := exists_mem_core_conj H hzH' hu hmk
    refine Subgroup.mem_map.2 ⟨p * h, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      have : p * h * ⟨z, hzH⟩ * (p * h)⁻¹ = ⟨z, hzH⟩ := by
        calc p * h * ⟨z, hzH⟩ * (p * h)⁻¹ = p * (h * ⟨z, hzH⟩ * h⁻¹) * p⁻¹ := by group
          _ = p * (p⁻¹ * ⟨z, hzH⟩ * p) * p⁻¹ := by rw [← hpu]
          _ = ⟨z, hzH⟩ := by group
      have h2 : p * h * ⟨z, hzH⟩ = ⟨z, hzH⟩ * (p * h) := (mul_inv_eq_iff_eq_mul.1 this)
      exact congrArg Subtype.val h2
    · have : mkH H p = 1 := (mkH_eq_one_iff H).2 hp
      change mkH H (p * h) = mkH H h
      rw [map_mul, this, one_mul]
  · intro hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hc
    have : c * ⟨z, hzH⟩ = ⟨z, hzH⟩ * c := Subtype.ext hc
    change mkH H c * mkH H ⟨z, hzH⟩ = mkH H ⟨z, hzH⟩ * mkH H c
    rw [← map_mul, ← map_mul, this]

end Cen

section Hom

variable (H : Subgroup G) {z : G} (hCH : Cen z ≤ H)

@[expose] def cenMk : ↥(Cen z) →* HBar H := (mkH H).comp (Subgroup.inclusion hCH)

omit [Finite G] in
theorem cenMk_apply (c : ↥(Cen z)) : cenMk H hCH c = mkH H ⟨(c : G), hCH c.2⟩ := rfl

omit [Finite G] in
theorem range_cenMk : (cenMk H hCH).range = barIn H (Cen z) := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨(c : G), hCH c.2⟩, by
      rw [Subgroup.mem_subgroupOf]; exact c.2, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_subgroupOf] at hx
    exact ⟨⟨(x : G), hx⟩, rfl⟩

theorem ker_cenMk_le : (cenMk H hCH).ker ≤ pPrimeCore 2 ↥(Cen z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_sSup ⟨inferInstance, ?_⟩
  refine Nat.coprime_two_left.2 ?_
  have hinj : Function.Injective
      (((Subgroup.inclusion hCH).comp (Subgroup.subtype (cenMk H hCH).ker)).codRestrict
        (pPrimeCore 2 ↥H) (fun k => (mkH_eq_one_iff H).1 k.2)) := by
    intro a b hab
    have := congrArg (fun w : ↥(pPrimeCore 2 ↥H) => (w : ↥H)) hab
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val this))
  exact Odd.of_dvd_nat (odd_card_pPrimeCore H) (Subgroup.card_dvd_of_injective _ hinj)

omit [Finite G] in
theorem cenMk_mem (c : ↥(Cen z)) : cenMk H hCH c ∈ barIn H (Cen z) := by
  rw [← range_cenMk H hCH]
  exact ⟨c, rfl⟩

@[expose] noncomputable def cenToBar : ↥(barIn H (Cen z)) →* CentralizerBar z :=
  ((MonoidHom.liftOfSurjective (cenMk H hCH).rangeRestrict
    (cenMk H hCH).rangeRestrict_surjective)
    ⟨toBar z, by
      rw [MonoidHom.ker_rangeRestrict]
      intro c hc
      have := ker_cenMk_le H hCH hc
      change toBar z c = 1
      exact (QuotientGroup.eq_one_iff c).2 this⟩).comp
    (Subgroup.inclusion (range_cenMk H hCH).ge)

theorem cenToBar_cenMk (c : ↥(Cen z)) : cenToBar H hCH ⟨cenMk H hCH c, cenMk_mem H hCH c⟩ = toBar z c := by
  unfold cenToBar
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c

theorem cenToBar_surjective : Function.Surjective (cenToBar H hCH) := by
  intro y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(Cen z)) y
  exact ⟨⟨cenMk H hCH c, cenMk_mem H hCH c⟩, cenToBar_cenMk H hCH c⟩

theorem odd_orderOf_of_cenToBar_eq_one (y : ↥(barIn H (Cen z))) (hy : cenToBar H hCH y = 1) :
    Odd (orderOf y) := by
  obtain ⟨y, hyC⟩ := y
  have hmem : y ∈ (cenMk H hCH).range := (range_cenMk H hCH) ▸ hyC
  obtain ⟨c, rfl⟩ := hmem
  have h1 : toBar z c = 1 := by
    rw [← cenToBar_cenMk H hCH c]
    exact hy
  have hcO : c ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff c).1 h1
  have hodd := odd_orderOf_of_mem_pPrimeCore hcO
  have hdvd : orderOf (⟨cenMk H hCH c, hyC⟩ : ↥(barIn H (Cen z))) ∣ orderOf c := by
    have : orderOf (cenMk H hCH c) ∣ orderOf c := orderOf_map_dvd _ _
    rwa [← Subgroup.orderOf_coe] 
  exact Odd.of_dvd_nat hodd hdvd

end Hom



section Syl

variable (H : Subgroup G) {z : G} {k : Kind} {S : Subgroup G}

theorem barIn_sylow (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hSH : S ≤ H) :
    ∃ T : Sylow 2 (HBar H), (T : Subgroup (HBar H)) = barIn H S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.ABGLocalTools.isSylowOf_iff).1 hS
  have hidx : ¬ 2 ∣ S.index := by
    have := h.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have h1 : IsPGroup 2 ↥(S.subgroupOf H) := h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hP : IsPGroup 2 ↥(barIn H S) := h1.map (mkH H)
  have hdvd1 : (barIn H S).index ∣ (S.subgroupOf H).index :=
    Subgroup.index_map_dvd (S.subgroupOf H) (QuotientGroup.mk'_surjective _)
  have hdvd2 : (S.subgroupOf H).index ∣ S.index :=
    Dvd.intro _ (Subgroup.relIndex_mul_index hSH)
  exact ⟨hP.toSylow (fun hd => hidx (hd.trans (hdvd1.trans hdvd2))), IsPGroup.toSylow_coe _ _⟩

end Syl

end CFSG.GH74.GLS.Stage2.Local.P34
