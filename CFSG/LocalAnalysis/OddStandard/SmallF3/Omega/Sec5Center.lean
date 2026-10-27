module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec5_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem sec5_oddCore_ne_top_of_twoU43 [Finite G] {L : Subgroup G}
    (h : IsTwoU43 (L ⧸ oddCore L)) : oddCore ↥L ≠ ⊤ := by
  intro htop
  haveI : Subsingleton (↥L ⧸ oddCore ↥L) := (QuotientGroup.subsingleton_iff).mpr htop
  haveI : Finite (↥L ⧸ oddCore ↥L) := inferInstance
  have h1 : Nat.card (Subgroup.center (↥L ⧸ oddCore ↥L)) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr inferInstance
  have h2 : Nat.card (Subgroup.center (↥L ⧸ oddCore ↥L)) = 2 := h.1
  omega

private theorem sec5_center_map_of_isQuasisimple [Finite G] {L : Subgroup G} (hL : IsQuasisimple L)
    (hne : oddCore ↥L ≠ ⊤) :
    (Subgroup.center ↥L).map (QuotientGroup.mk' (oddCore ↥L)) =
      Subgroup.center (↥L ⧸ oddCore ↥L) := by
  haveI : Group.IsPerfect ↥L := hL.1
  exact CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
    (QuotientGroup.mk' (oddCore ↥L)) (QuotientGroup.mk'_surjective _)
    (by
      rw [show (QuotientGroup.mk' (oddCore ↥L)).ker = oddCore ↥L from QuotientGroup.ker_mk' _]
      exact oddCore_le_center_of_isQuasisimple hL hne)

private theorem sec5_eq_of_ne_one_of_card_center {Q : Type*} [Group Q]
    (hcard : Nat.card (Subgroup.center Q) = 2) {a b : Subgroup.center Q} (ha : a ≠ 1)
    (hb : b ≠ 1) : a = b := by
  obtain ⟨y, hy1, hy2⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q)).mp hcard
  exact (hy2 a ha).trans (hy2 b hb).symm

theorem sec5_exists_central_involution [Finite G] {L : Subgroup G} (hL : IsOm6Z2 L) :
    ∃ u ∈ centerIn L, orderOf u = 2 := by
  let N : Subgroup ↥L := oddCore ↥L
  let Q := ↥L ⧸ N
  let q : ↥L →* Q := QuotientGroup.mk' N
  haveI : N.Normal := oddCore_normal ↥L
  have hcardCQ : Nat.card (Subgroup.center Q) = 2 := hL.2.1
  have hne : N ≠ ⊤ := sec5_oddCore_ne_top_of_twoU43 hL.2
  have hcenter : (Subgroup.center ↥L).map q = Subgroup.center Q :=
    sec5_center_map_of_isQuasisimple hL.1 hne
  have hoddN : Odd (Nat.card N) := sec5_odd_card_oddCore ↥L
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Nat.card (Subgroup.center Q) := by rw [hcardCQ]
  obtain ⟨c, hc2⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2 h2dvd
  let cQ : Q := c
  have hcQ2 : cQ ^ 2 = 1 := by
    change (c : Q) ^ 2 = 1
    rw [← hc2, ← Subgroup.orderOf_coe c, pow_orderOf_eq_one]
  have hcQne : cQ ≠ 1 := by
    intro h
    have hc1 : c = 1 := Subtype.ext h
    rw [hc1, orderOf_one] at hc2
    norm_num at hc2
  have hcQmem : cQ ∈ (Subgroup.center ↥L).map q := by
    rw [hcenter]
    exact c.2
  obtain ⟨x, hxcenter, hxq⟩ := Subgroup.mem_map.mp hcQmem
  have hx2N : x ^ 2 ∈ N := by
    rw [← QuotientGroup.ker_mk' (N := N), MonoidHom.mem_ker]
    change q (x ^ 2) = 1
    rw [map_pow, hxq, hcQ2]
  have hx2pow : (x ^ 2) ^ Nat.card N = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact N.orderOf_dvd_natCard hx2N
  let u : ↥L := x ^ Nat.card N
  have hu2 : u ^ 2 = 1 := by
    show (x ^ Nat.card N) ^ 2 = 1
    rw [← pow_mul, mul_comm (Nat.card N) 2, pow_mul]
    exact hx2pow
  have hqu : q u = cQ := by
    show q (x ^ Nat.card N) = cQ
    rw [map_pow, hxq]
    obtain ⟨t, ht⟩ := hoddN
    rw [ht, pow_add, pow_mul, hcQ2, one_pow, one_mul, pow_one]
  have hune : u ≠ 1 := by
    intro h
    have : q u = 1 := by rw [h, map_one]
    rw [hqu] at this
    exact hcQne this
  have huord : orderOf u = 2 := orderOf_eq_prime hu2 hune
  have hu_center : u ∈ Subgroup.center ↥L :=
    (Subgroup.center ↥L).pow_mem hxcenter (Nat.card N)
  exact ⟨(u : G), by rw [centerIn]; exact Subgroup.mem_map.mpr ⟨u, hu_center, rfl⟩,
    by rw [Subgroup.orderOf_coe, huord]⟩

theorem sec5_mem_zpowers_of_twoElement [Finite G] {L : Subgroup G} (hL : IsOm6Z2 L) {u : G}
    (hu : u ∈ centerIn L) (hu2 : orderOf u = 2) {x : G} (hx : x ∈ centerIn L)
    (hx2 : ∃ k : ℕ, orderOf x = 2 ^ k) : x ∈ zpowers u := by
  let N : Subgroup ↥L := oddCore ↥L
  let Q := ↥L ⧸ N
  let q : ↥L →* Q := QuotientGroup.mk' N
  haveI : N.Normal := oddCore_normal ↥L
  have hcardCQ : Nat.card (Subgroup.center Q) = 2 := hL.2.1
  have hne : N ≠ ⊤ := sec5_oddCore_ne_top_of_twoU43 hL.2
  have hcenter : (Subgroup.center ↥L).map q = Subgroup.center Q :=
    sec5_center_map_of_isQuasisimple hL.1 hne
  have hoddN : Odd (Nat.card N) := sec5_odd_card_oddCore ↥L
  have huL : u ∈ L := (sec5_mem_centerIn_iff.mp hu).1
  have hxL : x ∈ L := (sec5_mem_centerIn_iff.mp hx).1
  let u' : ↥L := ⟨u, huL⟩
  let x' : ↥L := ⟨x, hxL⟩
  have hu'c : u' ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using ((sec5_mem_centerIn_iff.mp hu).2 y y.2).symm
  have hx'c : x' ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using ((sec5_mem_centerIn_iff.mp hx).2 y y.2).symm
  have hu'ord : orderOf u' = 2 := by rw [Subgroup.orderOf_mk, hu2]
  obtain ⟨k, hk⟩ := hx2
  have hx'ord : orderOf x' = 2 ^ k := by rw [Subgroup.orderOf_mk, hk]
  have hqu'c : q u' ∈ Subgroup.center Q := by
    rw [← hcenter]
    exact Subgroup.mem_map_of_mem q hu'c
  have hqu'ne : q u' ≠ 1 := by
    intro h
    have hu'N : u' ∈ N := by
      rw [← QuotientGroup.ker_mk' (N := N), MonoidHom.mem_ker]
      exact h
    have hdvd : orderOf u' ∣ Nat.card N := N.orderOf_dvd_natCard hu'N
    rw [hu'ord] at hdvd
    exact absurd (hoddN.of_dvd_nat hdvd) (by decide)
  have hqu'sq : (q u') ^ 2 = 1 := by
    have h2 : u' ^ 2 = 1 := by rw [← hu'ord, pow_orderOf_eq_one]
    rw [← map_pow, h2, map_one]
  have hqu'ord : orderOf (q u') = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hqu'sq hqu'ne
  have hzle : Subgroup.zpowers (q u') ≤ Subgroup.center Q := Subgroup.zpowers_le.mpr hqu'c
  have hzcard : Nat.card (Subgroup.zpowers (q u')) = 2 := by
    rw [Nat.card_zpowers, hqu'ord]
  have hzeq : Subgroup.zpowers (q u') = Subgroup.center Q := by
    refine Subgroup.eq_of_le_of_card_ge hzle ?_
    rw [hzcard, hcardCQ]
  have hqx'c : q x' ∈ Subgroup.center Q := by
    rw [← hcenter]
    exact Subgroup.mem_map_of_mem q hx'c
  by_cases hqx'1 : q x' = 1
  · have hx'N : x' ∈ N := by
      rw [← QuotientGroup.ker_mk' (N := N), MonoidHom.mem_ker]
      exact hqx'1
    have hdvd : orderOf x' ∣ Nat.card N := N.orderOf_dvd_natCard hx'N
    have hodd_k : Odd (2 ^ k) := by
      rw [← hx'ord]
      exact hoddN.of_dvd_nat hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨by decide, hk0⟩)) hodd_k
    have hx'1 : x' = 1 := by
      apply orderOf_eq_one_iff.mp
      rw [hx'ord, hk0]
      norm_num
    have hx1 : x = 1 := congrArg Subtype.val hx'1
    rw [hx1]
    exact Subgroup.one_mem _
  · have hqu'x' : q u' = q x' := by
      have h1 : (⟨q u', hqu'c⟩ : Subgroup.center Q) ≠ 1 := by
        intro h
        exact hqu'ne (Subtype.ext_iff.mp h)
      have h2 : (⟨q x', hqx'c⟩ : Subgroup.center Q) ≠ 1 := by
        intro h
        exact hqx'1 (Subtype.ext_iff.mp h)
      exact congrArg Subtype.val (sec5_eq_of_ne_one_of_card_center hcardCQ h1 h2)
    have hyN : x' * u'⁻¹ ∈ N := by
      rw [← QuotientGroup.ker_mk' (N := N), MonoidHom.mem_ker]
      change q (x' * u'⁻¹) = 1
      rw [map_mul, map_inv, hqu'x']
      exact mul_inv_cancel (q x')
    have hcomm : Commute x' u' := Subgroup.mem_center_iff.mp hu'c x'
    have hy'_dvd : orderOf (x' * u'⁻¹) ∣ 2 ^ (k + 1) := by
      have hc : Commute x' u'⁻¹ := hcomm.inv_right
      refine (hc.orderOf_mul_dvd_mul_orderOf).trans ?_
      rw [hx'ord, orderOf_inv, hu'ord, pow_succ]
    have hodd_y : Odd (orderOf (x' * u'⁻¹)) :=
      hoddN.of_dvd_nat (N.orderOf_dvd_natCard hyN)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy'_dvd
    have hj0 : j = 0 := by
      by_contra hjne
      rw [hj] at hodd_y
      exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨by decide, hjne⟩)) hodd_y
    have hy'1 : x' * u'⁻¹ = 1 := by
      apply orderOf_eq_one_iff.mp
      rw [hj, hj0]
      norm_num
    have hx'u' : x' = u' := by
      have : x' * u'⁻¹ = 1 := hy'1
      exact mul_inv_eq_one.mp this
    have hxu : x = u := congrArg Subtype.val hx'u'
    rw [hxu]
    exact Subgroup.mem_zpowers u

theorem sec5_twoCoreIn_le_centerIn [Finite G] {L : Subgroup G} (hL : IsQuasisimple L) :
    twoCoreIn L ≤ centerIn L := by
  have hOpen : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1, hL.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hOpen
    (CFSG.pCore 2 ↥L) with hle | htop
  · intro x hx
    rw [twoCoreIn] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [centerIn]
    exact Subgroup.mem_map_of_mem L.subtype (hle hy)
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hPtop : IsPGroup 2 (⊤ : Subgroup ↥L) := htop ▸ CFSG.pCore_isPGroup
    have hP : IsPGroup 2 ↥L := hPtop.of_equiv Subgroup.topEquiv
    haveI : Group.IsPerfect ↥L := hL.1
    haveI : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hOpen
    haveI : Group.IsNilpotent ↥L := hP.isNilpotent
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance

theorem sec5_zpowers_le_twoCoreIn [Finite G] {L : Subgroup G} {u : G} (hu : u ∈ centerIn L)
    (hu2 : orderOf u = 2) : zpowers u ≤ twoCoreIn L := by
  have huL : u ∈ L := (sec5_mem_centerIn_iff.mp hu).1
  let u' : ↥L := ⟨u, huL⟩
  have hu'c : u' ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using ((sec5_mem_centerIn_iff.mp hu).2 y y.2).symm
  have hu'ord : orderOf u' = 2 := by rw [Subgroup.orderOf_mk, hu2]
  let N' : Subgroup ↥L := Subgroup.zpowers u'
  haveI : N'.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hu'c)
  have hN'p : IsPGroup 2 N' :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu'ord]; norm_num)
  have hN'le : N' ≤ CFSG.pCore 2 ↥L :=
    le_sSup (show N' ∈ {K : Subgroup ↥L | K.Normal ∧ IsPGroup 2 K} from ⟨inferInstance, hN'p⟩)
  have hmap : (Subgroup.zpowers u').map L.subtype = Subgroup.zpowers u := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [twoCoreIn, ← hmap]
  exact Subgroup.map_mono hN'le

end CFSG.OddStandard.SmallF3.Omega
