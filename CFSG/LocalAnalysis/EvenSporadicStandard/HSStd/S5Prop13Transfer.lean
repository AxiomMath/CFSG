module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Prop13Basic
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.EvenSporadicStandard.HSStd.Prop13

open Subgroup CFSG.EvenSporadicStandard.HSStd

variable {H : Type} [Group H]

theorem standard_subgroupOf_of_involution [Finite H] {A X : Subgroup H} (hAX : A ≤ X) {t : H}
    (htX : t ∈ X) (ht : orderOf t = 2) (htC : t ∈ centralizer (A : Set H))
    (hA : CFSG.Open.standardComponentIsStandard A) :
    CFSG.Open.standardComponentIsStandard (A.subgroupOf X) :=
  CFSG.Open.standardComponentIsStandard.subgroupOf hA hAX
    (CFSG.StandardSubgroupAPI.even_card_of_mem_of_orderOf_eq_two (Subgroup.mem_inf.2 ⟨htC, htX⟩) ht)

theorem oddCore_eq_bot_of_injective {Y G : Type} [Group Y] [Group G] [Finite Y] [Finite G]
    (ι : Y →* G) (hι : Function.Injective ι) (N : Subgroup G) [N.Normal] (hN : N ≤ ι.range)
    (hodd : ∀ y : Y, Odd (orderOf y) → ι y ∈ N) (hG : CFSG.oddCore G = ⊥) :
    CFSG.oddCore Y = ⊥ := by
  have hRodd : Odd (Nat.card (CFSG.oddCore Y)) := Transfer.card_oddCore_odd Y
  have hRN : (CFSG.oddCore Y).map ι ≤ N := by
    rintro _ ⟨r, hr, rfl⟩
    apply hodd
    have h1 : orderOf (⟨r, hr⟩ : CFSG.oddCore Y) ∣ Nat.card (CFSG.oddCore Y) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hRodd h1
  have hnormN : ((CFSG.oddCore Y).map ι |>.subgroupOf N).Normal := by
    refine ⟨fun x hx n => ?_⟩
    obtain ⟨y, hy⟩ := hN n.2
    obtain ⟨r, hr, hrx⟩ := hx
    refine ⟨y * r * y⁻¹, (inferInstance : (CFSG.oddCore Y).Normal).conj_mem r hr y, ?_⟩
    show ι (y * r * y⁻¹) = (n : G) * (x : G) * (n : G)⁻¹
    rw [map_mul, map_mul, map_inv, hy, hrx]
    rfl
  have hcard : Odd (Nat.card ((CFSG.oddCore Y).map ι |>.subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv,
      Subgroup.card_map_of_injective hι]
    exact hRodd
  have hle : ((CFSG.oddCore Y).map ι |>.subgroupOf N) ≤ CFSG.oddCore N :=
    le_sSup ⟨hnormN, hcard⟩
  have h2 := Subgroup.map_mono (f := N.subtype) hle
  rw [map_subgroupOf_eq_of_le hRN] at h2
  have h3 := h2.trans (Transfer.oddCore_map_subtype_le N)
  rw [hG, le_bot_iff] at h3
  exact (Subgroup.map_eq_bot_iff_of_injective _ hι).1 h3

theorem mem_of_odd_orderOf {M X : Subgroup H} {x : H} (hsq : ∀ y ∈ X, y ^ 2 ∈ M) (hx : x ∈ X)
    (hodd : Odd (orderOf x)) : x ∈ M := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : x ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one x
  have h2 : (x ^ 2) ^ (k + 1) = x := by
    calc (x ^ 2) ^ (k + 1) = x ^ (2 * k + 1) * x := by
          rw [← pow_mul, ← pow_succ]
          congr 1
      _ = x := by rw [h1, one_mul]
  rw [← h2]
  exact pow_mem (hsq x hx) _

theorem sq_mem_of_mem_sup_zpowers {M : Subgroup H} [M.Normal] {t : H} (ht : orderOf t = 2)
    {x : H} (hx : x ∈ M ⊔ zpowers t) : x ^ 2 ∈ M := by
  obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  have ht1 := mul_self_eq_one_of_orderOf ht
  rcases mem_zpowers_cases ht hz with h | h
  · rw [h]
    simpa [pow_two] using M.mul_mem hm hm
  · rw [h]
    have h1 : (m * t) ^ 2 = m * (t * m * t⁻¹) := by
      calc (m * t) ^ 2 = m * (t * m * t⁻¹) * (t * t) := by rw [pow_two]; group
        _ = m * (t * m * t⁻¹) := by rw [ht1, mul_one]
    rw [h1]
    exact M.mul_mem hm (Subgroup.Normal.conj_mem inferInstance m hm t)

theorem pRank_two_centralizer_subgroupOf [Finite H] {A X : Subgroup H} (hAX : A ≤ X) {t : H}
    (htX : t ∈ X) (ht : orderOf t = 2) (htC : t ∈ centralizer (A : Set H))
    (hrank : CFSG.Open.pRank 2 (centralizer (A : Set H)) = 1) :
    CFSG.Open.pRank 2 (centralizer ((A.subgroupOf X : Subgroup X) : Set X)) = 1 := by
  have hp : 1 < 2 := by norm_num
  have hC : centralizer ((A.subgroupOf X : Subgroup X) : Set X) =
      (centralizer (A : Set H)).subgroupOf X := Transfer.centralizer_subgroupOf hAX
  rw [hC]
  apply le_antisymm
  · calc CFSG.Open.pRank 2 ((centralizer (A : Set H)).subgroupOf X)
        ≤ CFSG.Open.pRank 2 (((centralizer (A : Set H)).subgroupOf X).map X.subtype) :=
          CFSG.SectionRank.pRank_le_map hp X.subtype X.subtype_injective _
      _ ≤ CFSG.Open.pRank 2 (centralizer (A : Set H)) := by
          refine CFSG.SectionRank.pRank_mono hp ?_
          rw [Subgroup.subgroupOf_map_subtype]
          exact inf_le_left
      _ = 1 := hrank
  · have ht' : (⟨t, htX⟩ : X) ∈ (centralizer (A : Set H)).subgroupOf X := htC
    have hord : orderOf (⟨t, htX⟩ : X) = 2 := by rw [Subgroup.orderOf_mk, ht]
    refine CFSG.SectionRank.le_pRank hp (E := zpowers (⟨t, htX⟩ : X)) ?_ ?_ (k := 1) ?_
    · rw [Subgroup.zpowers_le]
      exact ht'
    · refine ⟨inferInstance, fun y hy => ?_⟩
      have hg2 : (⟨t, htX⟩ : X) ^ 2 = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one _
      rcases mem_zpowers_cases hord hy with h | h
      · rw [h, one_pow]
      · rw [h, hg2]
    · rw [Nat.card_zpowers, hord]
      norm_num

theorem relIndex_sup_zpowers_le_two [Finite H] {M : Subgroup H} [M.Normal] {t : H}
    (ht : orderOf t = 2) :
    M.relIndex (M ⊔ zpowers t) ≤ 2 := by
  have hle : zpowers t ≤ M ⊔ zpowers t := le_sup_right
  let f : ↥(zpowers t) → ↥(M ⊔ zpowers t) ⧸ M.subgroupOf (M ⊔ zpowers t) :=
    fun z => QuotientGroup.mk ⟨(z : H), hle z.2⟩
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm, z, hz, hxz⟩ := Subgroup.mem_sup_of_normal_left.1 x.2
    refine ⟨⟨z, hz⟩, ?_⟩
    show (QuotientGroup.mk ⟨z, hle hz⟩ : ↥(M ⊔ zpowers t) ⧸ M.subgroupOf (M ⊔ zpowers t)) =
      QuotientGroup.mk x
    rw [QuotientGroup.eq]
    show z⁻¹ * (x : H) ∈ M
    rw [← hxz, ← mul_assoc]
    exact Subgroup.Normal.conj_mem' inferInstance m hm z
  calc M.relIndex (M ⊔ zpowers t)
      = Nat.card (↥(M ⊔ zpowers t) ⧸ M.subgroupOf (M ⊔ zpowers t)) := rfl
    _ ≤ Nat.card ↥(zpowers t) := Nat.card_le_card_of_surjective f hf
    _ = 2 := by rw [Nat.card_zpowers, ht]

theorem commute_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2)
    (a b : G) : a * b = b * a := by
  have h0 : 0 < Nat.card G := Nat.card_pos
  rcases (by omega : Nat.card G = 1 ∨ Nat.card G = 2) with h1 | h2
  · have := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Subsingleton.elim _ _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : IsCyclic G := isCyclic_of_prime_card (p := 2) h2
    exact mul_comm' a b

end CFSG.EvenSporadicStandard.HSStd.Prop13
