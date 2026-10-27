module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelTight

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ClassicalInvolution CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped MatrixGroups commutatorElement

theorem commutator_self_le {H : Type*} [Group H] (L : Subgroup H) : ⁅L, L⁆ ≤ L :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)

variable {K : Type} [Group K]

theorem mem_oddCenter_top {z : K} :
    z ∈ oddCenter (⊤ : Subgroup K) ↔ z ∈ center K ∧ Odd (orderOf z) := by
  rw [mem_oddCenter_iff, Subgroup.mem_center_iff]
  simp

instance oddCenter_top_normal : (oddCenter (⊤ : Subgroup K)).Normal :=
  ⟨fun n hn g => by
    have hc : n ∈ center K := (mem_oddCenter_top.mp hn).1
    rw [show g * n * g⁻¹ = n by rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]]
    exact hn⟩

theorem oddCenter_top_le_center : oddCenter (⊤ : Subgroup K) ≤ center K :=
  fun _ h => (mem_oddCenter_top.mp h).1

theorem eq_one_of_mem_oddCenter_top {z : K} (hz : z ∈ oddCenter (⊤ : Subgroup K)) {k : ℕ}
    (hzk : z ^ (2 ^ k) = 1) : z = 1 := by
  have hodd := (mem_oddCenter_top.mp hz).2
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have hcop : Nat.Coprime (orderOf z) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h1)

theorem commutator_self_eq_of_perfect {H : Type*} [Group H] {L : Subgroup H}
    (hL : Group.IsPerfect L) : ⁅L, L⁆ = L := by
  have := congrArg (Subgroup.map L.subtype) hL.commutator_eq_top
  rwa [_root_.commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at this

structure IsSL2Lift (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O)) (L' : Subgroup K) :
    Prop where
  map_eq : L'.map (QuotientGroup.mk' O) = L
  inf_eq_bot : L' ⊓ O = ⊥
  normalizer_le : ∀ k ∈ normalizer ((L.comap (QuotientGroup.mk' O)) : Set K),
    k ∈ normalizer (L' : Set K)
  sq_mem : ∀ x ∈ L.comap (QuotientGroup.mk' O), x ^ 2 = 1 → x ∈ L'

theorem exists_mul_mem_of_map_eq {O : Subgroup K} [O.Normal] {L : Subgroup (K ⧸ O)}
    {L' : Subgroup K} (hmap : L'.map (QuotientGroup.mk' O) = L) {x : K}
    (hx : x ∈ L.comap (QuotientGroup.mk' O)) : ∃ l ∈ L', l⁻¹ * x ∈ O := by
  rw [mem_comap, ← hmap] at hx
  obtain ⟨l, hl, hlx⟩ := hx
  refine ⟨l, hl, ?_⟩
  rw [← QuotientGroup.eq]
  exact hlx

theorem sq_mem_of_inf_eq_bot {L' : Subgroup K} {L : Subgroup (K ⧸ oddCenter (⊤ : Subgroup K))}
    (hmap : L'.map (QuotientGroup.mk' _) = L) (hinf : L' ⊓ oddCenter ⊤ = ⊥) {x : K}
    (hx : x ∈ L.comap (QuotientGroup.mk' _)) (hx2 : x ^ 2 = 1) : x ∈ L' := by
  obtain ⟨l, hl, ho⟩ := exists_mul_mem_of_map_eq hmap hx
  set o := l⁻¹ * x
  have hoc : o ∈ center K := oddCenter_top_le_center ho
  have hxlo : x = l * o := by simp [o]
  have ho2 : o ^ 2 = (l ^ 2)⁻¹ := by
    have h1 : (l * o) ^ 2 = l ^ 2 * o ^ 2 := by
      rw [sq, sq, sq, mul_assoc, ← mul_assoc o l o, ← (Subgroup.mem_center_iff.mp hoc l)]
      group
    rw [← hxlo, hx2] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hmem : o ^ 2 ∈ L' ⊓ oddCenter ⊤ :=
    mem_inf.mpr ⟨ho2 ▸ inv_mem (pow_mem hl 2), pow_mem ho 2⟩
  rw [hinf, mem_bot] at hmem
  have ho1 : o = 1 := eq_one_of_mem_oddCenter_top ho (k := 1) (by simpa using hmem)
  rw [hxlo, ho1, mul_one]
  exact hl

theorem not_dvd_card_oddCenter [Finite K] {p : ℕ} [Fact p.Prime]
    (hO : ∀ z ∈ oddCenter (⊤ : Subgroup K), z ^ p = 1 → z = 1) :
    ¬ p ∣ Nat.card (oddCenter (⊤ : Subgroup K)) := by
  intro hdvd
  obtain ⟨⟨z, hz⟩, hz2⟩ := exists_prime_orderOf_dvd_card' (G := oddCenter (⊤ : Subgroup K)) p hdvd
  rw [Subgroup.orderOf_mk] at hz2
  have h1 := hO z hz (by rw [← hz2]; exact pow_orderOf_eq_one z)
  rw [h1, orderOf_one] at hz2
  exact (Fact.out : p.Prime).one_lt.ne hz2

theorem exists_sl2Lift_of_four_le [Finite K] {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type}
    [Field F] [Finite F] (hFp : Nat.card F = p ^ e) (h4 : 4 ≤ Nat.card F)
    (hO : ∀ z ∈ oddCenter (⊤ : Subgroup K), z ^ p = 1 → z = 1)
    {L : Subgroup (K ⧸ oddCenter (⊤ : Subgroup K))} (eL : L ≃* SL(2, F)) :
    ∃ L' : Subgroup K, IsSL2Lift (oddCenter ⊤) L L' := by
  set O := oddCenter (⊤ : Subgroup K)
  set π := QuotientGroup.mk' O
  set Lh := L.comap π
  have hLperf : Group.IsPerfect L := isPerfect_of_equiv_sl2 h4 eL
  set L' := ⁅Lh, Lh⁆
  have hL'Lh : L' ≤ Lh := commutator_self_le Lh
  have hmap : L'.map π = L := by
    rw [Subgroup.map_commutator, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O),
      commutator_self_eq_of_perfect hLperf]
  have hcomm : ⁅L', L'⁆ = L' := by
    refine le_antisymm (commutator_self_le L') ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨l₁, hl₁, ho₁⟩ := exists_mul_mem_of_map_eq hmap ha
    obtain ⟨l₂, hl₂, ho₂⟩ := exists_mul_mem_of_map_eq hmap hb
    have h := commutatorElement_mul_center l₁ l₂ (oddCenter_top_le_center ho₁)
      (oddCenter_top_le_center ho₂)
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at h
    rw [h]
    exact commutator_mem_commutator hl₁ hl₂
  have hL'perf : Group.IsPerfect L' := by
    refine ⟨Subgroup.map_injective L'.subtype_injective ?_⟩
    rw [_root_.commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hcomm]
  have hinf : L' ⊓ O = ⊥ := by
    let ρ : L' →* L := (π.comp L'.subtype).codRestrict L (fun x => by
      rw [← hmap]; exact mem_map_of_mem _ x.2)
    have hρ : Function.Surjective ρ := by
      intro y
      obtain ⟨x, hx, hxy⟩ := (show (y : K ⧸ O) ∈ L'.map π by rw [hmap]; exact y.2)
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hker : ρ.ker = O.subgroupOf L' := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro h
        have := congrArg Subtype.val h
        simpa [ρ, π, QuotientGroup.eq_one_iff] using this
      · intro h
        exact Subtype.ext (by simpa [ρ, π, QuotientGroup.eq_one_iff] using h)
    let π' : L' →* SL(2, F) := eL.toMonoidHom.comp ρ
    have hπ'k : π'.ker = ρ.ker := by
      ext x
      simp [π', MonoidHom.mem_ker]
    have hcen : π'.ker ≤ center L' := by
      rw [hπ'k, hker]
      intro x hx
      rw [mem_subgroupOf] at hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (oddCenter_top_le_center hx)) g)
    have hcard : Odd (Nat.card π'.ker) ∧ ¬ p ∣ Nat.card π'.ker := by
      have hdvd : Nat.card π'.ker ∣ Nat.card O := by
        rw [hπ'k, hker, ← Subgroup.card_map_of_injective L'.subtype_injective,
          subgroupOf_map_subtype]
        exact card_dvd_of_le inf_le_left
      exact ⟨(odd_card_oddCenter _).of_dvd_nat hdvd,
        fun h => not_dvd_card_oddCenter hO (h.trans hdvd)⟩
    have hbot := ModelFacts.OddCover.sl2_noCover (K := F) hp2 hFp L' π'
      (eL.surjective.comp hρ) hcen hcard
    rw [hπ'k, hker] at hbot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : L') ∈ O.subgroupOf L' := mem_subgroupOf.mpr hx.2
    rw [hbot, mem_bot] at this
    rw [mem_bot]
    exact congrArg Subtype.val this
  refine ⟨L', hmap, hinf, fun k hk => ?_, fun x hx hx2 => sq_mem_of_inf_eq_bot hmap hinf hx hx2⟩
  have hconj : ∀ g ∈ normalizer (Lh : Set K), conjSubgroup g L' = L' := by
    intro g hg
    have h1 : conjSubgroup g Lh = Lh := by
      rw [conjSubgroup_eq_rightConjugate, rightConjugate_eq_self_iff]
      exact inv_mem hg
    simp only [conjSubgroup, L'] at h1 ⊢
    rw [Subgroup.map_commutator, h1]
  rw [← rightConjugate_eq_self_iff, show rightConjugate L' k = conjSubgroup k⁻¹ L' by
    rw [conjSubgroup_eq_rightConjugate, inv_inv]]
  exact hconj _ (inv_mem hk)

theorem sl2_zmod_three_pow_twelve : ∀ x : SL(2, ZMod 3), x ^ 12 = 1 := by
  decide +kernel

theorem sl2_pow_twelve_of_card_three {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3)
    (x : SL(2, F)) : x ^ 12 = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, h3, ZMod.card]
  set e' := sl2RingEquiv (FiniteField.ringEquivOfCardEq hcard)
  apply e'.injective
  rw [map_pow, map_one]
  exact sl2_zmod_three_pow_twelve _

theorem exists_sl2Lift_three [Finite K] {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3)
    (hO : ∀ z ∈ oddCenter (⊤ : Subgroup K), z ^ 3 = 1 → z = 1)
    {L : Subgroup (K ⧸ oddCenter (⊤ : Subgroup K))} (eL : L ≃* SL(2, F)) :
    ∃ L' : Subgroup K, IsSL2Lift (oddCenter ⊤) L L' := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFodd : Odd (Nat.card F) := by rw [h3]; decide
  set O := oddCenter (⊤ : Subgroup K)
  set π := QuotientGroup.mk' O
  set Lh := L.comap π
  have hOLh : O ≤ Lh := fun z hz => by
    rw [mem_comap, show π z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
    exact one_mem _
  set N := O.subgroupOf Lh
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have hc := oddCenter_top_le_center hn
    rw [show ((g * n * g⁻¹ : Lh) : K) = n by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]]
    exact hn⟩
  let ρ : Lh →* L := (π.comp Lh.subtype).codRestrict L (fun x => x.2)
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective O (y : K ⧸ O)
    exact ⟨⟨x, show π x ∈ L by rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  have hρk : ρ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h' : π x = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff (x : K)).mp h'
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff (x : K)).mpr h)
  have hidx : N.index = Nat.card L := by
    rw [← hρk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρs, card_top]
  have hcardN : Nat.card N = Nat.card O := Nat.card_congr (subgroupOfEquivOfLe hOLh).toEquiv
  have hcop : Nat.Coprime (Nat.card O) (Nat.card L) := by
    refine Nat.coprime_of_dvd fun r hr hrO hrL => ?_
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L) r hrL
    have hr12 : r ∣ 12 := by
      rw [← hy]
      apply orderOf_dvd_of_pow_eq_one
      apply eL.injective
      rw [map_pow, map_one]
      exact sl2_pow_twelve_of_card_three h3 _
    have hr23 : r = 2 ∨ r = 3 := by
      have h12 : (12 : ℕ) = 2 ^ 2 * 3 := rfl
      rw [h12] at hr12
      rcases (Nat.Prime.dvd_mul hr).mp hr12 with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)
    rcases hr23 with rfl | rfl
    · exact (Nat.not_even_iff_odd.mpr (odd_card_oddCenter _)) (even_iff_two_dvd.mpr hrO)
    · exact not_dvd_card_oddCenter hO hrO
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime
    (show Nat.Coprime (Nat.card N) N.index by rw [hcardN, hidx]; exact hcop)
  set m := Nat.card H'
  have hm : m = Nat.card L := by
    have h1 := hH'.card_mul_card
    have h2 := N.card_mul_index
    rw [hidx] at h2
    have hpos : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have hmcop : Nat.Coprime (Nat.card O) m := hm ▸ hcop
  have hchar : ∀ x : Lh, x ∈ H' ↔ x ^ m = 1 := by
    intro x
    constructor
    · intro hx
      have : (⟨x, hx⟩ : H') ^ Nat.card H' = 1 := pow_card_eq_one'
      exact congrArg Subtype.val this
    · intro hxm
      obtain ⟨⟨⟨n, hn⟩, ⟨h, hh⟩⟩, rfl⟩ := hH'.2 x
      have hnc : (n : K) ∈ center K := oddCenter_top_le_center (mem_subgroupOf.mp hn)
      have hcomm : Commute n h := Subtype.ext ((Subgroup.mem_center_iff.mp hnc) h).symm
      have hhm : (⟨h, hh⟩ : H') ^ Nat.card H' = 1 := pow_card_eq_one'
      rw [hcomm.mul_pow, show h ^ m = 1 from congrArg Subtype.val hhm, mul_one] at hxm
      have hn1 : n = 1 := by
        have h1 : orderOf n ∣ m := orderOf_dvd_of_pow_eq_one hxm
        have h2 : orderOf n ∣ Nat.card O := by
          rw [← hcardN]
          have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
          rwa [Subgroup.orderOf_mk] at this
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hmcop h2 h1)
      show n * h ∈ H'
      rw [hn1, one_mul]
      exact hh
  set L' := H'.map Lh.subtype
  have hmemL' : ∀ x : K, x ∈ L' ↔ ∃ hx : x ∈ Lh, (⟨x, hx⟩ : Lh) ^ m = 1 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using (hchar y).mp hy⟩
    · rintro ⟨hx, hxm⟩
      exact ⟨⟨x, hx⟩, (hchar _).mpr hxm, rfl⟩
  have hmap : L'.map π = L := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      exact x.2
    · obtain ⟨x, hx⟩ := hρs ⟨y, hy⟩
      obtain ⟨⟨⟨n, hn⟩, ⟨h, hh⟩⟩, hnh⟩ := hH'.2 x
      refine ⟨(h : K), ⟨h, hh, rfl⟩, ?_⟩
      have h1 : ρ x = ρ h := by
        rw [← hnh, map_mul, (show ρ n = 1 by rw [← MonoidHom.mem_ker, hρk]; exact hn), one_mul]
      rw [hx] at h1
      exact (congrArg Subtype.val h1).symm
  have hinf : L' ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, hy, rfl⟩, hxO⟩
    have hyN : y ∈ N := mem_subgroupOf.mpr hxO
    have : y ∈ N ⊓ H' := mem_inf.mpr ⟨hyN, hy⟩
    rw [hH'.disjoint.eq_bot, mem_bot] at this
    rw [mem_bot, this]
    rfl
  refine ⟨L', hmap, hinf, fun k hk => ?_, fun x hx hx2 => ?_⟩
  · rw [mem_normalizer_iff]
    intro x
    rw [hmemL', hmemL']
    constructor
    · rintro ⟨hx, hxm⟩
      refine ⟨(mem_normalizer_iff.mp hk x).mp hx, Subtype.ext ?_⟩
      have := congrArg Subtype.val hxm
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
      rw [conj_pow, this]
      group
    · rintro ⟨hx, hxm⟩
      refine ⟨(mem_normalizer_iff.mp hk x).mpr hx, Subtype.ext ?_⟩
      have := congrArg Subtype.val hxm
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
      rw [conj_pow] at this
      have h1 : x ^ m = k⁻¹ * (k * x ^ m * k⁻¹) * k := by group
      rw [h1, this]
      group
  · rw [hmemL']
    refine ⟨hx, Subtype.ext ?_⟩
    have h2m : 2 ∣ m := by
      rw [hm]
      have := orderOf_dvd_natCard (eL.symm (-1))
      rwa [MulEquiv.orderOf_eq, orderOf_eq_prime (neg_one_sq) (sl2_neg_one_ne_one hFodd)] at this
    obtain ⟨c, hc⟩ := h2m
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [hc, pow_mul, hx2, one_pow]

theorem exists_sl2Lift [Finite K] {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F]
    [Finite F] (hFp : Nat.card F = p ^ e)
    (hO : ∀ z ∈ oddCenter (⊤ : Subgroup K), z ^ p = 1 → z = 1)
    {L : Subgroup (K ⧸ oddCenter (⊤ : Subgroup K))} (eL : L ≃* SL(2, F)) :
    ∃ L' : Subgroup K, IsSL2Lift (oddCenter ⊤) L L' := by
  by_cases h3 : Nat.card F = 3
  · have hp3 : p = 3 := by
      have h : p ^ e = 3 := hFp.symm.trans h3
      exact ((Nat.Prime.pow_eq_iff Nat.prime_three).mp h).1
    subst hp3
    exact exists_sl2Lift_three h3 hO eL
  · have hFodd : Odd (Nat.card F) := by
      rw [hFp]
      exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    have h4 : 4 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rcases hFodd with ⟨m, hm⟩
      omega
    exact exists_sl2Lift_of_four_le hp2 hFp h4 hO eL

variable {F : Type} [Field F] [Finite F]

theorem inf_oddCenter_eq_bot {J : Subgroup K} (e : J ≃* SL(2, F)) (hF : Odd (Nat.card F)) :
    J ⊓ oddCenter (⊤ : Subgroup K) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxJ, hxO⟩
  have hc : x ∈ centralizer (J : Set K) := by
    rw [mem_centralizer_iff]
    intro g _
    exact (Subgroup.mem_center_iff.mp (oddCenter_top_le_center hxO) g)
  rcases eq_one_or_centralInv_of_mem_centralizer e hxJ hc with h | h
  · rw [mem_bot, h]
  · exfalso
    have hodd := (mem_oddCenter_top.mp hxO).2
    rw [h, orderOf_centralInv e hF] at hodd
    exact absurd hodd (by decide)

@[expose] noncomputable def mapOddCenterEquiv {J : Subgroup K} (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F)) : J.map (QuotientGroup.mk' (oddCenter (⊤ : Subgroup K))) ≃* SL(2, F) :=
  have hinj : Function.Injective
      ((QuotientGroup.mk' (oddCenter (⊤ : Subgroup K))).comp J.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      have : (x : K) ∈ J ⊓ oddCenter ⊤ := mem_inf.mpr ⟨x.2, hx⟩
      rw [inf_oddCenter_eq_bot e hF, mem_bot] at this
      exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  ((MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])).trans
    (MonoidHom.ofInjective hinj).symm).trans e

theorem centralInv_mapOddCenterEquiv {J : Subgroup K} (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F)) :
    centralInv (mapOddCenterEquiv e hF) =
      QuotientGroup.mk' (oddCenter (⊤ : Subgroup K)) (centralInv e) := by
  rfl

theorem exists_lift_of_centralizer [Finite K] {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hFp : Nat.card F = p ^ e) (hO : ∀ z ∈ oddCenter (⊤ : Subgroup K), z ^ p = 1 → z = 1)
    {z : K} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    {L' : Subgroup (K ⧸ oddCenter (⊤ : Subgroup K))} (eL : L' ≃* SL(2, F))
    (hNL : centralizer ({QuotientGroup.mk' _ z} : Set (K ⧸ oddCenter (⊤ : Subgroup K))) ≤
      normalizer (L' : Set _))
    (hzL : QuotientGroup.mk' _ z ∈ L') :
    ∃ L : Subgroup K, L.map (QuotientGroup.mk' (oddCenter ⊤)) = L' ∧ L ≤ centralizer {z} ∧
      centralizer {z} ≤ normalizer (L : Set K) ∧ Nonempty (L ≃* SL(2, F)) ∧ z ∈ L := by
  have hFodd : Odd (Nat.card F) := by
    rw [hFp]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  set O := oddCenter (⊤ : Subgroup K)
  set π := QuotientGroup.mk' O
  obtain ⟨L, hL⟩ := exists_sl2Lift hp2 hFp hO eL
  have hinj : Function.Injective (π.comp L.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have : (x : K) ∈ L ⊓ O := mem_inf.mpr ⟨x.2, hx⟩
    rw [hL.inf_eq_bot, mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hrange : (π.comp L.subtype).range = L' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hL.map_eq]
  let eLL : L ≃* SL(2, F) :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans eL
  have hzLh : z ∈ L'.comap π := hzL
  have hzLt : z ∈ L := hL.sq_mem z hzLh hz2
  have hzc : z = centralInv eLL := (eq_one_or_centralInv_of_sq eLL hFodd hzLt hz2).resolve_left hz1
  refine ⟨L, hL.map_eq, fun l hl => ?_, fun k hk => hL.normalizer_le k ?_, ⟨eLL⟩, hzLt⟩
  · rw [mem_centralizer_singleton_iff, hzc]
    exact (mem_centralizer_iff.mp (centralInv_mem_centralizer eLL) l hl)
  ·
    rw [mem_centralizer_singleton_iff] at hk
    have hk' : π k ∈ centralizer ({π z} : Set (K ⧸ O)) := by
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hk]
    have hN := hNL hk'
    rw [mem_normalizer_iff] at hN ⊢
    intro x
    rw [mem_comap, mem_comap, map_mul, map_mul, map_inv]
    exact hN (π x)

section Descent

variable [Finite K] {J : Subgroup K} (e : J ≃* SL(2, F))

omit [Finite K] in
theorem centralizer_le_normalizer_quot (hF : Odd (Nat.card F))
    (hCZ : centralizer ({centralInv e} : Set K) ≤ normalizer (J : Set K)) :
    centralizer ({centralInv (mapOddCenterEquiv e hF)} :
        Set (K ⧸ oddCenter (⊤ : Subgroup K))) ≤
      normalizer ((J.map (QuotientGroup.mk' (oddCenter ⊤)) : Subgroup _) : Set _) := by
  set O := oddCenter (⊤ : Subgroup K)
  set π := QuotientGroup.mk' O
  set z := centralInv e
  rw [centralInv_mapOddCenterEquiv]
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective O x
  rw [mem_centralizer_singleton_iff] at hx
  set o := k * z * k⁻¹ * z⁻¹
  have ho : o ∈ O := by
    rw [← QuotientGroup.eq_one_iff (N := O) o]
    show π o = 1
    simp only [o, map_mul, map_inv]
    rw [show π k * π z = π z * π k from hx]
    group
  have hoc := oddCenter_top_le_center ho
  have hz2 : z ^ 2 = 1 := centralInv_sq e
  have hkz : k * z * k⁻¹ = o * z := by simp [o]
  have ho2 : o ^ 2 = 1 := by
    have h1 : (k * z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, hz2]; group
    have hcomm : Commute o z := (Subgroup.mem_center_iff.mp hoc z).symm
    rwa [hkz, hcomm.mul_pow, hz2, mul_one] at h1
  have ho1 : o = 1 := eq_one_of_mem_oddCenter_top ho (k := 1) (by simpa using ho2)
  have hkC : k ∈ centralizer ({z} : Set K) := by
    rw [mem_centralizer_singleton_iff]
    have : k * z * k⁻¹ = z := by rw [hkz, ho1, one_mul]
    calc k * z = (k * z * k⁻¹) * k := by group
      _ = z * k := by rw [this]
  exact le_normalizer_map π (mem_map_of_mem π (hCZ hkC))

theorem eq_or_eq_quot {p e' : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hFp : Nat.card F = p ^ e')
    (hO : ∀ z ∈ oddCenter (⊤ : Subgroup K), z ^ p = 1 → z = 1) {B : Subgroup K}
    (hU : ∀ L : Subgroup K, L ≤ centralizer ({centralInv e} : Set K) →
      centralizer ({centralInv e} : Set K) ≤ normalizer (L : Set K) →
      Nonempty (L ≃* SL(2, F)) → centralInv e ∈ L → L = J ∨ L = B)
    (hF : Odd (Nat.card F)) (L' : Subgroup (K ⧸ oddCenter (⊤ : Subgroup K)))
    (_h1 : L' ≤ centralizer ({centralInv (mapOddCenterEquiv e hF)} : Set _))
    (h2 : centralizer ({centralInv (mapOddCenterEquiv e hF)} : Set _) ≤ normalizer (L' : Set _))
    (h3 : Nonempty (L' ≃* SL(2, F))) (h4 : centralInv (mapOddCenterEquiv e hF) ∈ L') :
    L' = J.map (QuotientGroup.mk' (oddCenter ⊤)) ∨
      L' = B.map (QuotientGroup.mk' (oddCenter ⊤)) := by
  rw [centralInv_mapOddCenterEquiv] at h2 h4
  obtain ⟨eL⟩ := h3
  obtain ⟨L, hmap, hLC, hCN, hLe, hzL⟩ := exists_lift_of_centralizer hp2 hFp hO
    (centralInv_sq e) (centralInv_ne_one e hF) eL h2 h4
  rcases hU L hLC hCN hLe hzL with h | h
  · left
    rw [← hmap, h]
  · right
    rw [← hmap, h]

theorem exists_involution_lift_quot (u : K ⧸ oddCenter (⊤ : Subgroup K)) (hu : orderOf u = 2) :
    ∃ v : K, orderOf v = 2 ∧ QuotientGroup.mk' (oddCenter ⊤) v = u := by
  obtain ⟨v₀, rfl⟩ := QuotientGroup.mk'_surjective (oddCenter (⊤ : Subgroup K)) u
  obtain ⟨k, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos v₀).ne'
  have hu2 : (QuotientGroup.mk' (oddCenter (⊤ : Subgroup K)) v₀) ^ 2 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one _
  have hπ : QuotientGroup.mk' (oddCenter (⊤ : Subgroup K)) (v₀ ^ r) =
      QuotientGroup.mk' (oddCenter (⊤ : Subgroup K)) v₀ := by
    rw [map_pow]
    obtain ⟨s, rfl⟩ := hr
    rw [pow_succ, pow_mul, hu2, one_pow, one_mul]
  have hsq : (v₀ ^ r) ^ 2 ∈ oddCenter (⊤ : Subgroup K) := by
    rw [← QuotientGroup.eq_one_iff (N := oddCenter (⊤ : Subgroup K))]
    show QuotientGroup.mk' (oddCenter (⊤ : Subgroup K)) ((v₀ ^ r) ^ 2) = 1
    rw [map_pow, hπ, hu2]
  have h2k : ((v₀ ^ r) ^ 2) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, ← pow_mul, show r * (2 * 2 ^ k) = orderOf v₀ * 2 by rw [hor]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  have hv2 : (v₀ ^ r) ^ 2 = 1 := eq_one_of_mem_oddCenter_top hsq h2k
  have hv1 : v₀ ^ r ≠ 1 := by
    intro h
    have : QuotientGroup.mk' (oddCenter (⊤ : Subgroup K)) v₀ = 1 := by rw [← hπ, h, map_one]
    rw [this, orderOf_one] at hu
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨v₀ ^ r, orderOf_eq_prime hv2 hv1, hπ⟩

theorem isConj_quot (hconj : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (x y : K ⧸ oddCenter (⊤ : Subgroup K)) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  obtain ⟨x₀, hx₀, rfl⟩ := exists_involution_lift_quot x hx
  obtain ⟨y₀, hy₀, rfl⟩ := exists_involution_lift_quot y hy
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj x₀ y₀ hx₀ hy₀)
  exact isConj_iff.mpr ⟨QuotientGroup.mk' (oddCenter ⊤) c, by
    rw [← map_mul, ← map_inv, ← map_mul, hc]⟩

end Descent

end CFSG.ComponentClassification.RankTwoOddLie
