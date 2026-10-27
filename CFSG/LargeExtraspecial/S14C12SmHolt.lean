module

public import CFSG.LargeExtraspecial.S14C12SmQ
public import CFSG.LargeExtraspecial.S14C12SmAlt
public import CFSG.RankThree.Holt.CommutingGraph
public import CFSG.Timmesfeld.Bridge.NoPolarConnected

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SmithHolt

open Subgroup CFSG.Open CFSG.Timmesfeld.Connectivity CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

theorem sq_mul_facts {d e : G} (hd : orderOf d = 2) (he : e * e = 1)
    (h4 : orderOf (d * e) = 4) :
    orderOf ((d * e) ^ 2) = 2 ∧ d * (d * e) ^ 2 = (d * e) ^ 2 * d ∧ d ≠ (d * e) ^ 2 := by
  have hd2 : d * d = 1 := by rw [← _root_.sq, ← hd, pow_orderOf_eq_one]
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hsq : (e * d) ^ 2 = (d * e) ^ 2 := by
    have h1 : (d * e) ^ 2 * (d * e) ^ 2 = 1 := by
      rw [← pow_add, show 2 + 2 = orderOf (d * e) by rw [h4], pow_orderOf_eq_one]
    rw [← inv_eq_of_mul_eq_one_right h1, ← inv_pow, mul_inv_rev, hdi, hei]
  refine ⟨?_, ?_, fun h => ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← pow_mul, show 2 * 2 = orderOf (d * e) by rw [h4], pow_orderOf_eq_one]
    · have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [h4] at h2
      norm_num at h2
  · calc d * (d * e) ^ 2 = (d * d) * e * d * e := by rw [_root_.sq]; group
      _ = e * d * e := by rw [hd2, one_mul]
      _ = (e * d) * (e * d) * d := by
        rw [show (e * d) * (e * d) * d = e * d * e * (d * d) by group, hd2, mul_one]
      _ = (d * e) ^ 2 * d := by rw [← _root_.sq, hsq]
  · have h1 : e * d * e = 1 := by
      calc e * d * e = d⁻¹ * (d * e) ^ 2 := by rw [_root_.sq]; group
        _ = 1 := by rw [← h, inv_mul_cancel]
    have h2 : d = 1 := by
      calc d = e⁻¹ * (e * d * e) * e⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, hei, he]
    rw [h2, orderOf_one] at hd
    exact absurd hd (by norm_num)

theorem exists_sylow_twoCentral [Finite G] (S : Setting G) :
    ∃ P : Sylow 2 G, S.z ∈ (P : Subgroup G) ∧ (P : Subgroup G) ≤ centralizer {S.z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_le_M S
  refine ⟨P, ?_, hP⟩
  have hz : IsPGroup 2 (zpowers S.z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.orderOf_z, pow_one])
  have hcomm : ∀ p ∈ (P : Subgroup G), S.z * p * S.z⁻¹ = p := fun p hp => by
    rw [← mem_centralizer_singleton_iff.mp (hP hp), mul_inv_cancel_right]
  have hzN : S.z ∈ normalizer ((P : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      rw [hcomm p hp]
      exact hp
    · intro hp
      have h1 := hcomm _ hp
      have h2 : p = S.z * p * S.z⁻¹ := by
        calc p = S.z⁻¹ * (S.z * p * S.z⁻¹) * S.z := by group
          _ = S.z⁻¹ * (S.z * (S.z * p * S.z⁻¹) * S.z⁻¹) * S.z := by rw [h1]
          _ = S.z * p * S.z⁻¹ := by group
      rw [h2]
      exact hp
  have hmem : S.z ∈ zpowers S.z ⊓ normalizer ((P : Subgroup G) : Set G) :=
    ⟨mem_zpowers _, hzN⟩
  exact ((hz.inf_normalizer_sylow P).le hmem).2

theorem false_of_isStronglyEmbedded [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : CFSG.IsStronglyEmbedded H) {d e : G} (hd : orderOf d = 2)
    (he : orderOf e = 2) (h4 : orderOf (d * e) = 4) : False := by
  have hd2 : d * d = 1 := by rw [← _root_.sq, ← hd, pow_orderOf_eq_one]
  have he2 : e * e = 1 := by rw [← _root_.sq, ← he, pow_orderOf_eq_one]
  obtain ⟨hz2, hcomm, hne⟩ := sq_mul_facts hd he2 h4
  have h2G : 2 ∣ Nat.card G := hd ▸ orderOf_dvd_natCard d
  rcases bender_strongly_embedded_normal_series G H hH with
    hS | ⟨M, N, hM, hN, hMN, -, hMo, hNo, hB⟩
  · have hNC := CFSG.Timmesfeld.Bridge.noCommutingDistinctInvolutions_of_sylow hS
    exact hne (congrArg Subtype.val (hNC ⟨d, hd⟩ ⟨(d * e) ^ 2, hz2⟩ hcomm))
  · have hM1 : M = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
      · exact h
      · exfalso
        rw [h, Subgroup.card_top] at hMo
        exact (Nat.not_even_iff_odd.mpr hMo) (even_iff_two_dvd.mpr h2G)
    have hdN : d ∈ N := CFSG.Timmesfeld.Bridge.mem_of_odd_index hNo hd2
    have heN : e ∈ N := CFSG.Timmesfeld.Bridge.mem_of_odd_index hNo he2
    set π : N →* N ⧸ M.subgroupOf N := QuotientGroup.mk' (M.subgroupOf N)
    have hinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hM1, Subgroup.bot_subgroupOf]
    have hord : ∀ (x : G) (hx : x ∈ N), orderOf (π ⟨x, hx⟩) = orderOf x := fun x hx => by
      rw [orderOf_injective π hinj, Subgroup.orderOf_mk]
    refine CFSG.Timmesfeld.Bridge.not_orderOf_mul_eq_four_of_fusionIsBenderGroup hB
      (s := π ⟨d, hdN⟩) (t := π ⟨e, heN⟩) (by rw [hord]; exact hd) (by rw [hord]; exact he) ?_
    rw [← map_mul, show (⟨d, hdN⟩ : N) * ⟨e, heN⟩ = ⟨d * e, N.mul_mem hdN heN⟩ from rfl, hord,
      h4]

theorem reach_conjugatesOf [Finite G] [IsSimpleGroup G]
    (hHolt : HoltUniqueFixedPointSimple) (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6))
    {d e : G} (hd : IsConj S.z d) (he : IsConj S.z e) (h4 : orderOf (d * e) = 4)
    {t : G} (ht : IsConj S.z t) : Reach (conjugatesOf S.z) S.z t := by
  by_contra hnt
  have hd2 := SmithQ.mul_self_eq_one_of_isConj S hd
  have he2 := SmithQ.mul_self_eq_one_of_isConj S he
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    refine ⟨d, e, fun hc => ?_⟩
    have h1 : (d * e) ^ 2 = 1 := by
      rw [_root_.sq, show d * e * (d * e) = d * (e * d) * e by group, ← hc,
        show d * (d * e) * e = (d * d) * (e * e) by group, hd2, he2, one_mul]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [h4] at h2
    norm_num at h2
  rcases RankThree.Holt.holt_commutingComponent hHolt hnonab S.orderOf_z
      (exists_sylow_twoCentral S) ⟨t, ht, hnt⟩ with ⟨H, hH⟩ | ⟨m, -, ⟨φ⟩⟩
  · exact false_of_isStronglyEmbedded hH (S.orderOf_of_isConj hd) (S.orderOf_of_isConj he) h4
  · exact SmithAlt.false_of_mulEquiv_alternatingGroup S hw hU φ

end SmithHolt

end CFSG.LargeExtraspecial.S14
