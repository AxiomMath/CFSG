module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentInitial.PerfectFixedCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_of_pow_eq_one_of_isCyclic {Y T : Subgroup G} [Finite Y] (hYc : IsCyclic Y)
    (hTY : T ≤ Y) {n : ℕ} (hn : 0 < n) (hT : Nat.card T = n) {y : G} (hyY : y ∈ Y)
    (hy : y ^ n = 1) : y ∈ T := by
  classical
  have : Fintype Y := Fintype.ofFinite Y
  set S := (Finset.univ : Finset Y).filter (fun a : Y => a ^ n = 1) with hS
  set T' := (Finset.univ : Finset Y).filter (fun a : Y => (a : G) ∈ T) with hT'
  have hTcard : T'.card = n := by
    rw [← hT, hT', ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv
  have hsub : T' ⊆ S := fun a ha => by
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, Subtype.ext ?_⟩
    have h1 := pow_card_eq_one' (G := T) (x := ⟨a, ha.2⟩)
    rw [hT] at h1
    simpa using congrArg Subtype.val h1
  have hScard : S.card ≤ n := IsCyclic.card_pow_eq_one_le hn
  have heq : T' = S := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hyS : (⟨y, hyY⟩ : Y) ∈ S :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, Subtype.ext (by simpa using hy)⟩
  rw [← heq] at hyS
  exact (Finset.mem_filter.1 hyS).2

theorem extraspecial_cyclic_product_characteristic_exponent_four_layer
    {D E Y T : Subgroup G} [Finite D] (_hD : IsPGroup 2 D)
    (hY : Y = (center D).map D.subtype) (hYc : IsCyclic Y) {k : ℕ} (_hk : 2 ≤ k)
    (_hYk : Nat.card Y = 2 ^ k) {z : G} (hzY : z ∈ Y) (hz : orderOf z = 2) (hED : E ≤ D)
    (hE : IsExtraspecialPGroup 2 E) (hDEY : D = E ⊔ Y) (hEY : E ⊓ Y = zpowers z)
    (hZE : (center E).map E.subtype = zpowers z) (hTY : T ≤ Y) (hT : Nat.card T = 4) :
    {d : G | d ∈ D ∧ d ^ 4 = 1} = ((E ⊔ T : Subgroup G) : Set G) ∧
      ((E ⊔ T).subgroupOf D).Characteristic ∧
      ¬ IsMulCommutative (E ⊔ T : Subgroup G) ∧
      (∀ d ∈ E ⊔ T, d ^ 4 = 1) ∧
      (center (E ⊔ T : Subgroup G)).map (E ⊔ T).subtype = T ∧
      ⁅E ⊔ T, E ⊔ T⁆ = zpowers z ∧
      (∀ d ∈ D, orderOf d = 2 → d ∈ E ⊔ T) ∧
      (∀ d ∈ D, orderOf d = 2 → d ≠ z →
        d ∈ E ⊔ T ∧ d ∉ (center (E ⊔ T : Subgroup G)).map (E ⊔ T).subtype) ∧
      (∀ P : Subgroup G, D ≤ P → (D.subgroupOf P).Characteristic →
        ((E ⊔ T).subgroupOf P).Characteristic) ∧
      normalizer (D : Set G) ≤ normalizer ((E ⊔ T : Subgroup G) : Set G) := by
  classical
  have hYD : ∀ y ∈ Y, y ∈ D ∧ ∀ d ∈ D, d * y = y * d := by
    intro y hy
    rw [hY] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨w.2, fun d hd => congrArg Subtype.val (mem_center_iff.1 hw ⟨d, hd⟩)⟩
  have hYle : Y ≤ D := fun y hy => (hYD y hy).1
  have hTD : T ≤ D := hTY.trans hYle
  have : Finite Y := Finite.of_injective _ (Subgroup.inclusion_injective hYle)
  have : Finite E := Finite.of_injective _ (Subgroup.inclusion_injective hED)
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    norm_num at hz
  have hE4 : ∀ x ∈ E, x ^ 4 = 1 := by
    intro x hx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq := (CFSG.GroupTheory.frattini_elementary_quotient hE.1).2.2.1
      (QuotientGroup.mk (⟨x, hx⟩ : E))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hE.2.2.1] at hq
    have hx2 : x ^ 2 ∈ zpowers z := by
      rw [← hZE]
      exact ⟨_, hq, rfl⟩
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hx2
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hz2, one_zpow]
  have hT4 : ∀ y ∈ Y, (y ^ 4 = 1 ↔ y ∈ T) := by
    intro y hy
    refine ⟨fun h4 => mem_of_pow_eq_one_of_isCyclic hYc hTY (by norm_num) hT hy h4, fun hyT => ?_⟩
    have h1 := pow_card_eq_one' (G := T) (x := ⟨y, hyT⟩)
    rw [hT] at h1
    simpa using congrArg Subtype.val h1
  have hzT : z ∈ T := (hT4 z hzY).1 (by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hz2, one_pow])
  have hzE : z ∈ E := by
    have : z ∈ E ⊓ Y := by rw [hEY]; exact mem_zpowers z
    exact this.1
  have hYN : Y ≤ normalizer (E : Set G) :=
    le_trans (fun y hy => mem_centralizer_iff.2 fun x hx => (hYD y hy).2 x (hED hx))
      (centralizer_le_normalizer _)
  have hTN : T ≤ normalizer (E : Set G) := hTY.trans hYN
  have hDmem : ∀ d ∈ D, ∃ x ∈ E, ∃ y ∈ Y, x * y = d := by
    intro d hd
    rw [hDEY, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left E Y hYN, Set.mem_mul] at hd
    simpa using hd
  have hLmem : ∀ d ∈ E ⊔ T, ∃ x ∈ E, ∃ t ∈ T, x * t = d := by
    intro d hd
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left E T hTN, Set.mem_mul] at hd
    simpa using hd
  have hLD : E ⊔ T ≤ D := sup_le hED hTD
  have hL4 : ∀ d ∈ E ⊔ T, d ^ 4 = 1 := by
    intro d hd
    obtain ⟨x, hx, t, ht, rfl⟩ := hLmem d hd
    have hc : Commute x t := ((hYD t (hTY ht)).2 x (hED hx))
    rw [hc.mul_pow, hE4 x hx, (hT4 t (hTY ht)).2 ht, one_mul]
  have hset : {d : G | d ∈ D ∧ d ^ 4 = 1} = ((E ⊔ T : Subgroup G) : Set G) := by
    ext d
    constructor
    · rintro ⟨hd, hd4⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := hDmem d hd
      have hc : Commute x y := (hYD y hy).2 x (hED hx)
      rw [hc.mul_pow, hE4 x hx, one_mul] at hd4
      exact mul_mem (mem_sup_left hx) (mem_sup_right ((hT4 y hy).1 hd4))
    · intro hd
      exact ⟨hLD hd, hL4 d hd⟩
  have hmemL : ∀ d, d ∈ E ⊔ T ↔ d ∈ D ∧ d ^ 4 = 1 := fun d => by
    rw [← SetLike.mem_coe, ← hset]
    rfl
  have hEE : ⁅E, E⁆ = zpowers z := by
    rw [← hZE, ← hE.2.1, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      range_subtype]
  have hcomm : ⁅E ⊔ T, E ⊔ T⁆ = zpowers z := by
    refine le_antisymm ?_ (hEE ▸ commutator_mono le_sup_left le_sup_left)
    rw [commutator_le]
    intro a ha b hb
    obtain ⟨x, hx, t, ht, rfl⟩ := hLmem a ha
    obtain ⟨x', hx', t', ht', rfl⟩ := hLmem b hb
    rw [CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_mul_of_commute
      ((hYD t (hTY ht)).2 x' (hED hx')).symm ((hYD t (hTY ht)).2 t' (hTD ht')).symm
      ((hYD t' (hTY ht')).2 x (hED hx)).symm, ← hEE]
    exact commutator_mem_commutator hx hx'
  have hcenter : (center (E ⊔ T : Subgroup G)).map (E ⊔ T).subtype = T := by
    ext w
    rw [CFSG.LocalAnalysis.ComponentInitial.mem_map_center_iff]
    constructor
    · rintro ⟨hw, hwc⟩
      obtain ⟨x, hx, t, ht, rfl⟩ := hLmem w hw
      have hxZ : x ∈ zpowers z := by
        rw [← hZE]
        refine ⟨⟨x, hx⟩, mem_center_iff.2 fun e => Subtype.ext ?_, rfl⟩
        have h1 := hwc e (mem_sup_left e.2)
        have hte : t * e = e * t := ((hYD t (hTY ht)).2 e (hED e.2)).symm
        change (e : G) * x = x * e
        apply mul_right_cancel (b := t)
        calc (e : G) * x * t = e * (x * t) := by rw [mul_assoc]
          _ = x * t * e := h1
          _ = x * e * t := by rw [mul_assoc, hte, ← mul_assoc]
      have hxT : x ∈ T := by
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hxZ
        exact zpow_mem hzT m
      exact mul_mem hxT ht
    · intro hw
      exact ⟨mem_sup_right hw, fun d hd => (hYD w (hTY hw)).2 d (hLD hd)⟩
  have hchar : ∀ P : Subgroup G, D ≤ P → (D.subgroupOf P).Characteristic →
      ((E ⊔ T).subgroupOf P).Characteristic := by
    intro P _ hP
    refine characteristic_iff_map_le.2 fun φ x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [mem_subgroupOf] at hy ⊢
    have hyD : y ∈ D.subgroupOf P := mem_subgroupOf.2 (hLD hy)
    have hφD : φ y ∈ D.subgroupOf P := by
      rw [← (characteristic_iff_map_eq.1 hP) φ]
      exact ⟨y, hyD, rfl⟩
    refine (hmemL _).2 ⟨mem_subgroupOf.1 hφD, ?_⟩
    have hy4 : y ^ 4 = 1 := Subtype.ext (by simpa using hL4 _ hy)
    have : (φ y) ^ 4 = 1 := by rw [← map_pow, hy4, map_one]
    simpa using congrArg Subtype.val this
  refine ⟨hset, ?_, ?_, hL4, hcenter, hcomm, ?_, ?_, hchar, ?_⟩
  · refine characteristic_iff_map_le.2 fun φ x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [mem_subgroupOf] at hy ⊢
    refine (hmemL _).2 ⟨(φ y).2, ?_⟩
    have hy4 : y ^ 4 = 1 := Subtype.ext (by simpa using hL4 _ hy)
    have : (φ y) ^ 4 = 1 := by rw [← map_pow, hy4, map_one]
    simpa using congrArg Subtype.val this
  · intro hab
    have hbot : ⁅E ⊔ T, E ⊔ T⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hab.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    rw [hcomm] at hbot
    exact hz1 (by
      have : z ∈ zpowers z := mem_zpowers z
      rwa [hbot, mem_bot] at this)
  · intro d hd hd2
    refine (hmemL d).2 ⟨hd, ?_⟩
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← hd2, pow_orderOf_eq_one, one_pow]
  · intro d hd hd2 hdz
    refine ⟨(hmemL d).2 ⟨hd, ?_⟩, fun hdZ => ?_⟩
    · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← hd2, pow_orderOf_eq_one, one_pow]
    · rw [hcenter] at hdZ
      have hzle : zpowers z ≤ Y := zpowers_le.2 hzY
      have hdz' : d ∈ zpowers z := mem_of_pow_eq_one_of_isCyclic hYc hzle (n := 2) (by norm_num)
        (by rw [Nat.card_zpowers, hz]) (hTY hdZ) (by rw [← hd2, pow_orderOf_eq_one])
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hdz'
      have hm : z ^ m = z ^ (m % 2) := by rw [← zpow_mod_orderOf, hz]; norm_num
      rcases Int.emod_two_eq_zero_or_one m with h0 | h1
      · rw [hm, h0, zpow_zero, orderOf_one] at hd2
        norm_num at hd2
      · rw [hm, h1, zpow_one] at hdz
        exact hdz rfl
  · intro g hg
    rw [mem_normalizer_iff] at hg ⊢
    intro d
    rw [hmemL, hmemL, hg d]
    constructor
    · rintro ⟨hd, hd4⟩
      exact ⟨hd, by rw [conj_pow, hd4]; group⟩
    · rintro ⟨hd, hd4⟩
      refine ⟨hd, ?_⟩
      rw [conj_pow] at hd4
      calc d ^ 4 = g⁻¹ * (g * d ^ 4 * g⁻¹) * g := by group
        _ = 1 := by rw [hd4]; group

end CFSG.LocalAnalysis.GorensteinLyons
