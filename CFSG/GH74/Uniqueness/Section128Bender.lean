module

public import CFSG.GH74.Uniqueness.Section123

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem ncard_pairs_eq_mul {α β : Type*} [Finite α] [Finite β] (A : Set α) (B : α → Set β) (k : ℕ)
    (hB : ∀ a ∈ A, (B a).ncard = k) :
    {p : α × β | p.1 ∈ A ∧ p.2 ∈ B p.1}.ncard = A.ncard * k := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have h1 : {p : α × β | p.1 ∈ A ∧ p.2 ∈ B p.1} =
      ↑(Finset.univ.filter fun p : α × β => p.1 ∈ A ∧ p.2 ∈ B p.1) := by
    ext p
    simp
  have h2 : A = ↑(Finset.univ.filter fun a : α => a ∈ A) := by
    ext a
    simp
  have h3 : ∀ a, B a = ↑(Finset.univ.filter fun b : β => b ∈ B a) := by
    intro a
    ext b
    simp
  rw [h1, Set.ncard_coe_finset, Finset.card_filter, Fintype.sum_prod_type]
  conv_rhs => rw [h2, Set.ncard_coe_finset, Finset.card_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ A
  · have hk := hB a ha
    rw [h3 a, Set.ncard_coe_finset] at hk
    simp only [ha, true_and, ite_true, one_mul]
    rw [← hk, Finset.card_filter]
  · simp [ha]

namespace Sec128B

theorem mul_self_of_orderOf_eq_two {H : Type*} [Group H] {x : H} (hx : orderOf x = 2) :
    x * x = 1 := by
  rw [← sq, ← hx]
  exact pow_orderOf_eq_one x

theorem ne_one_of_orderOf_eq_two {H : Type*} [Group H] {x : H} (hx : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hx
  omega

theorem orderOf_eq_two_of_mul_self {H : Type*} [Group H] {x : H} (hx : x * x = 1) (hx1 : x ≠ 1) :
    orderOf x = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hx) hx1

theorem exists_sylow_mem_of_orderOf_eq_two {K : Type*} [Group K] [Finite K] {a : K}
    (ha : orderOf a = 2) : ∃ Q : Sylow 2 K, a ∈ (Q : Subgroup K) := by
  have hp : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  exact ⟨Q, hQ (mem_zpowers a)⟩

theorem mem_rootCenter_of_commute {K : Type*} [Group K] [Finite K] {q i e : ℕ} {Q : Subgroup K}
    {t : K} (hc : Bender.BenderCore q i e Q t) {z b : K} (hz : orderOf z = 2)
    (hzM : z ∈ Bender.borel Q) (hb : orderOf b = 2) (hcomm : z * b = b * z) :
    b ∈ Bender.rootCenter Q ∧ b ≠ 1 := by
  have hconj : b⁻¹ * z * b ∈ Bender.borel Q := by
    have h1 : b⁻¹ * z * b = z := by rw [mul_assoc, hcomm, inv_mul_cancel_left]
    rw [h1]
    exact hzM
  exact hc.involution_iff.mp ⟨hc.mem_borel_of_conj hzM hz hconj, hb⟩

end Sec128B

namespace Bender

theorem BenderType.ncard_involutions
    {K : Type*} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) :
    {a : K | orderOf a = 2}.ncard = (2 ^ n - 1) * ((2 ^ n) ^ i + 1) := by
  obtain ⟨t, hc⟩ := h.exists_benderCore (default : Sylow 2 K)
  obtain ⟨z, hz, hz1⟩ := hc.exists_involution
  have hz2 : orderOf z = 2 := (hc.involution_iff.mpr ⟨hz, hz1⟩).2
  have he : 0 < e := by
    rw [← hc.card_fixCartan]
    exact Nat.card_pos
  have hconj : {a : K | orderOf a = 2} = conjugatesOf z := by
    ext a
    constructor
    · intro ha
      exact hc.isConj_of_involutions (Sec128B.mul_self_of_orderOf_eq_two hz2) hz1
        (Sec128B.mul_self_of_orderOf_eq_two ha) (Sec128B.ne_one_of_orderOf_eq_two ha)
    · intro ha
      change orderOf a = 2
      rw [← hz2]
      exact (CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj ha).symm
  have hmul :=
    CFSG.ShultStronglyClosedTI.InvolutionCounting.card_centralizer_mul_card_conjugatesOf z
  rw [hc.card_centralizer hz hz1, hc.card_group, Nat.card_coe_set_eq] at hmul
  rw [hconj]
  have hpos : 0 < (2 ^ n) ^ i * e := Nat.mul_pos (by positivity) he
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [hmul]
  ring

theorem BenderType.ncard_commuting_involutions
    {K : Type*} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) {a : K} (ha : orderOf a = 2) :
    {b : K | orderOf b = 2 ∧ a * b = b * a}.ncard = 2 ^ n - 1 := by
  obtain ⟨Q, hQ⟩ := Sec128B.exists_sylow_mem_of_orderOf_eq_two ha
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hset : {b : K | orderOf b = 2 ∧ a * b = b * a} =
      ((rootCenter (Q : Subgroup K) : Subgroup K) : Set K) \ {1} := by
    ext b
    constructor
    · rintro ⟨hb, hcomm⟩
      exact Sec128B.mem_rootCenter_of_commute hc ha (le_borel _ hQ) hb hcomm
    · rintro ⟨hb, hb1⟩
      exact ⟨(hc.involution_iff.mpr ⟨hb, hb1⟩).2, (mem_rootCenter_iff.mp hb).2 a hQ⟩
  have hcard : ((rootCenter (Q : Subgroup K) : Subgroup K) : Set K).ncard = 2 ^ n := by
    rw [← Nat.card_coe_set_eq]
    exact hc.card_center
  rw [hset, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), hcard]

theorem BenderType.odd_orderOf_mul_iff
    {K : Type*} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) {a b : K} (ha : orderOf a = 2) (hb : orderOf b = 2) :
    Odd (orderOf (a * b)) ↔ a = b ∨ a * b ≠ b * a := by
  have ha2 := Sec128B.mul_self_of_orderOf_eq_two ha
  have hb2 := Sec128B.mul_self_of_orderOf_eq_two hb
  constructor
  · intro hodd
    by_contra hcon
    rw [not_or, not_not] at hcon
    obtain ⟨hne, hcomm⟩ := hcon
    have hab : orderOf (a * b) = 2 := by
      refine Sec128B.orderOf_eq_two_of_mul_self ?_ ?_
      · calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hcomm]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, one_mul]
      · intro h1
        apply hne
        rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hb2]
    rw [hab] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr even_two)
  · rintro (hab | hne)
    · rw [← hab, ha2, orderOf_one]
      exact odd_one
    · by_contra hodd
      obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hodd
      have hkpos : 0 < k := by
        have := orderOf_pos (a * b)
        omega
      obtain ⟨hv2, hv1, hav, hbv, -⟩ :=
        dihedral_even ha2 hb2 hkpos (by omega : orderOf (a * b) = 2 * k)
      have hv : orderOf ((a * b) ^ k) = 2 := Sec128B.orderOf_eq_two_of_mul_self hv2 hv1
      obtain ⟨Q, hQ⟩ := Sec128B.exists_sylow_mem_of_orderOf_eq_two hv
      obtain ⟨t, hc⟩ := h.exists_benderCore Q
      have hvM : (a * b) ^ k ∈ borel (Q : Subgroup K) := le_borel _ hQ
      have haR := Sec128B.mem_rootCenter_of_commute hc hv hvM ha hav.symm
      have hbR := Sec128B.mem_rootCenter_of_commute hc hv hvM hb hbv.symm
      exact hne ((mem_rootCenter_iff.mp hbR.1).2 a (mem_rootCenter_iff.mp haR.1).1)

theorem BenderType.ncard_oddPairs
    {K : Type*} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) :
    {p : K × K | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))}.ncard =
      (2 ^ n - 1) * ((2 ^ n) ^ i + 1) * ((2 ^ n) ^ i * (2 ^ n - 1) + 1) := by
  have hq : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := h.two_le.2; omega)
  have hfib : ∀ a ∈ {a : K | orderOf a = 2},
      {b : K | orderOf b = 2 ∧ Odd (orderOf (a * b))}.ncard = (2 ^ n) ^ i * (2 ^ n - 1) + 1 := by
    intro a ha
    have hset : {b : K | orderOf b = 2 ∧ Odd (orderOf (a * b))} =
        {b : K | orderOf b = 2} \ ({b : K | orderOf b = 2 ∧ a * b = b * a} \ {a}) := by
      ext b
      constructor
      · rintro ⟨hb, hodd⟩
        refine ⟨hb, ?_⟩
        rintro ⟨⟨-, hcomm⟩, hba⟩
        rcases (h.odd_orderOf_mul_iff ha hb).mp hodd with hab | hne
        · exact hba hab.symm
        · exact hne hcomm
      · rintro ⟨hb, hnot⟩
        refine ⟨hb, (h.odd_orderOf_mul_iff ha hb).mpr ?_⟩
        by_cases hab : a = b
        · exact Or.inl hab
        · right
          intro hcomm
          exact hnot ⟨⟨hb, hcomm⟩, fun hba => hab hba.symm⟩
    have hsub : {b : K | orderOf b = 2 ∧ a * b = b * a} \ {a} ⊆ {b : K | orderOf b = 2} :=
      fun b hb => hb.1.1
    have hmem : a ∈ {b : K | orderOf b = 2 ∧ a * b = b * a} := ⟨ha, rfl⟩
    rw [hset, Set.ncard_sdiff hsub, Set.ncard_sdiff_singleton_of_mem hmem,
      h.ncard_involutions, h.ncard_commuting_involutions ha]
    obtain ⟨r, hr⟩ : ∃ r, 2 ^ n - 1 = r + 1 := ⟨2 ^ n - 2, by omega⟩
    rw [hr]
    set s := (2 ^ n) ^ i
    have h1 : (r + 1) * (s + 1) = (s * (r + 1) + 1) + r := by ring
    omega
  have hset : {p : K × K | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} =
      {p : K × K | p.1 ∈ {a : K | orderOf a = 2} ∧
        p.2 ∈ (fun a : K => {b : K | orderOf b = 2 ∧ Odd (orderOf (a * b))}) p.1} := rfl
  rw [hset, ncard_pairs_eq_mul _ _ _ hfib, h.ncard_involutions]

end Bender

theorem ncard_oddPairs_quotient_center {G : Type} [Group G] [Finite G]
    (hodd : Odd (Nat.card (center G))) :
    {p : G × G | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))}.ncard =
      {p : (G ⧸ center G) × (G ⧸ center G) |
        orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))}.ncard := by
  let π : G →* G ⧸ center G := QuotientGroup.mk' (center G)
  have himg : ∀ a : G, orderOf a = 2 → orderOf (π a) = 2 := by
    intro a ha
    have h1 : π a ≠ 1 := fun h1 =>
      CFSG.OddInversion.notMem_of_odd_card hodd ha ((QuotientGroup.eq_one_iff a).mp h1)
    refine Sec128B.orderOf_eq_two_of_mul_self ?_ h1
    rw [← map_mul, Sec128B.mul_self_of_orderOf_eq_two ha, map_one]
  have hoddiff : ∀ x : G, Odd (orderOf x) ↔ Odd (orderOf (π x)) := by
    intro x
    refine ⟨fun hx => Odd.of_dvd_nat hx (orderOf_map_dvd π x), fun hx => ?_⟩
    have hz : x ^ orderOf (π x) ∈ center G := by
      have h1 : π (x ^ orderOf (π x)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hodd2 : Odd (orderOf (x ^ orderOf (π x))) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard (center G) hz)
    have hdvd : orderOf x ∣ orderOf (π x) * orderOf (x ^ orderOf (π x)) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact pow_orderOf_eq_one _)
    exact Odd.of_dvd_nat (hx.mul hodd2) hdvd
  have hinj : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → π a = π b → a = b := by
    intro a b ha hb hab
    exact A2.eq_of_inv_mul_mem_of_odd hodd le_rfl (Sec128B.mul_self_of_orderOf_eq_two ha)
      (Sec128B.mul_self_of_orderOf_eq_two hb) (QuotientGroup.eq.mp hab)
  have hlift : ∀ x : G ⧸ center G, orderOf x = 2 → ∃ a : G, orderOf a = 2 ∧ π a = x := by
    intro x hx
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    have hcN : c ∉ center G := fun hc =>
      Sec128B.ne_one_of_orderOf_eq_two hx ((QuotientGroup.eq_one_iff c).mpr hc)
    have hcc : c * c ∈ center G := (QuotientGroup.eq_one_iff (c * c)).mp (by
      rw [QuotientGroup.mk_mul]
      exact Sec128B.mul_self_of_orderOf_eq_two hx)
    obtain ⟨y, -, hy2, hyc⟩ := exists_involution_mem_zpowers_coset hodd hcc hcN
    refine ⟨y, hy2, ?_⟩
    have h1 : π (y * c⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hyc
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  have himageEq : Prod.map π π ''
      {p : G × G | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} =
      {p : (G ⧸ center G) × (G ⧸ center G) |
        orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, h⟩
      have h1 : π a = x := congrArg Prod.fst h
      have h2 : π b = y := congrArg Prod.snd h
      subst h1 h2
      exact ⟨himg a ha, himg b hb, by rw [← map_mul]; exact (hoddiff _).mp hab⟩
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨a, ha, rfl⟩ := hlift x hx
      obtain ⟨b, hb, rfl⟩ := hlift y hy
      refine ⟨(a, b), ⟨ha, hb, (hoddiff _).mpr ?_⟩, rfl⟩
      rw [map_mul]
      exact hxy
  have hinjOn : Set.InjOn (Prod.map π π)
      {p : G × G | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} := by
    rintro ⟨a, b⟩ ⟨ha, hb, -⟩ ⟨a', b'⟩ ⟨ha', hb', -⟩ h
    have h1 : π a = π a' := congrArg Prod.fst h
    have h2 : π b = π b' := congrArg Prod.snd h
    rw [hinj a a' ha ha' h1, hinj b b' hb hb' h2]
  rw [← himageEq, hinjOn.ncard_image]

theorem ncard_oddPairs_subgroup {X : Type*} [Group X] (H : Subgroup X) :
    {p : X × X | p.1 ∈ H ∧ orderOf p.1 = 2 ∧ p.2 ∈ H ∧ orderOf p.2 = 2 ∧
        Odd (orderOf (p.1 * p.2))}.ncard =
      {p : ↥H × ↥H | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))}.ncard := by
  have hinj : Function.Injective (Prod.map (Subtype.val : ↥H → X) (Subtype.val : ↥H → X)) :=
    Subtype.val_injective.prodMap Subtype.val_injective
  have himage : Prod.map (Subtype.val : ↥H → X) (Subtype.val : ↥H → X) ''
      {p : ↥H × ↥H | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} =
      {p : X × X | p.1 ∈ H ∧ orderOf p.1 = 2 ∧ p.2 ∈ H ∧ orderOf p.2 = 2 ∧
        Odd (orderOf (p.1 * p.2))} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, h⟩
      have h1 : (a : X) = x := congrArg Prod.fst h
      have h2 : (b : X) = y := congrArg Prod.snd h
      subst h1 h2
      refine ⟨a.2, ?_, b.2, ?_, ?_⟩
      · rw [Subgroup.orderOf_coe]
        exact ha
      · rw [Subgroup.orderOf_coe]
        exact hb
      · rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
        exact hab
    · rintro ⟨hx, hx2, hy, hy2, hxy⟩
      refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ⟨?_, ?_, ?_⟩, rfl⟩
      · show orderOf (⟨x, hx⟩ : H) = 2
        rw [Subgroup.orderOf_mk]
        exact hx2
      · show orderOf (⟨y, hy⟩ : H) = 2
        rw [Subgroup.orderOf_mk]
        exact hy2
      · show Odd (orderOf ((⟨x, hx⟩ : H) * ⟨y, hy⟩))
        rw [← Subgroup.orderOf_coe]
        exact hxy
  rw [← himage, Set.ncard_image_of_injective _ hinj]

theorem BenderSub.ncard_oddPairs
    {X : Type} [Group X] [Finite X] {Z : Set X} {M F : Subgroup X}
    {n i e : ℕ} (hB : BenderSub Z M F n i e) :
    {p : X × X | p.1 ∈ F ∧ orderOf p.1 = 2 ∧ p.2 ∈ F ∧ orderOf p.2 = 2 ∧
        Odd (orderOf (p.1 * p.2))}.ncard =
      (2 ^ n - 1) * ((2 ^ n) ^ i + 1) * ((2 ^ n) ^ i * (2 ^ n - 1) + 1) := by
  rw [ncard_oddPairs_subgroup F,
    ncard_oddPairs_quotient_center (A2.odd_card_center_of_benderSub hB)]
  exact hB.bender.ncard_oddPairs

end CFSG.GH74.Uniqueness
