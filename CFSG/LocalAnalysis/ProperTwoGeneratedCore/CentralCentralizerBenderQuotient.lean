module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderSquares

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1 CFSG.ShultStronglyClosedTI

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G}

instance escapingBar_zpowers_normal (x : G) : (Subgroup.zpowers (escapingBar x)).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr
    (Subgroup.mem_center_iff.mpr fun y => (commute_escapingBar y).eq))

abbrev BenderQuotient (x : G) := EscapingQuotient x ⧸ Subgroup.zpowers (escapingBar x)

abbrev benderMk (x : G) : EscapingQuotient x →* BenderQuotient x := QuotientGroup.mk' _

abbrev benderImage (H : Subgroup G) (x : G) : Subgroup (BenderQuotient x) :=
  (escapingImage H x).map (benderMk x)

theorem isInvolution_benderMk (hx : orderOf x = 2) {u : EscapingQuotient x} (hu : orderOf u = 2)
    (hux : u ≠ escapingBar x) : IsInvolution (benderMk x u) := by
  refine ⟨fun h => ?_, by rw [← map_pow, pow_two, mul_self_eq_one_of_orderOf_eq_two hu, map_one]⟩
  have hmem : u ∈ Subgroup.zpowers (escapingBar x) := by
    rwa [← QuotientGroup.ker_mk' (Subgroup.zpowers (escapingBar x)), MonoidHom.mem_ker]
  rcases eq_one_or_eq_of_mem_zpowers (escaping_orderOf_mk x (orderOf_escapingSelf hx)) hmem with
    h1 | h1
  · rw [h1, orderOf_one] at hu
    exact absurd hu (by decide)
  · exact hux h1

theorem exists_involution_lift_benderMk (hx : orderOf x = 2)
    (hsq : ∀ w : EscapingQuotient x, w ^ 2 ≠ escapingBar x) {y : BenderQuotient x}
    (hy : IsInvolution y) :
    ∃ u : EscapingQuotient x, benderMk x u = y ∧ orderOf u = 2 ∧ u ≠ escapingBar x := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have hu2 : u ^ 2 ∈ Subgroup.zpowers (escapingBar x) := by
    rw [← QuotientGroup.ker_mk' (Subgroup.zpowers (escapingBar x)), MonoidHom.mem_ker, map_pow]
    exact hy.2
  have hux : u ≠ escapingBar x := fun h => hy.1 (by
    rw [h]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _))
  rcases eq_one_or_eq_of_mem_zpowers (escaping_orderOf_mk x (orderOf_escapingSelf hx)) hu2 with
    h | h
  · refine ⟨u, rfl, orderOf_eq_prime h fun h1 => hy.1 ?_, hux⟩
    rw [h1, map_one]
  · exact absurd h (hsq u)

theorem eq_one_of_pow_two_pow_eq_one_of_odd {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : Odd (Nat.card K)) {a : Y} (ha : a ∈ K) {k : ℕ} (hk : a ^ 2 ^ k = 1) : a = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hK)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
    (Subgroup.orderOf_dvd_natCard K ha))

theorem mem_zpowers_of_comap_odd {N : Subgroup (BenderQuotient x)} (hN : Odd (Nat.card N))
    {p : EscapingQuotient x} (hp : p ∈ N.comap (benderMk x)) {k : ℕ} (hk : p ^ 2 ^ k = 1) :
    p ∈ Subgroup.zpowers (escapingBar x) := by
  rw [← QuotientGroup.ker_mk' (Subgroup.zpowers (escapingBar x)), MonoidHom.mem_ker]
  exact eq_one_of_pow_two_pow_eq_one_of_odd hN hp (by rw [← map_pow, hk, map_one])

namespace EscapingQuotientData

variable (hq : EscapingQuotientData H x)
include hq

theorem benderMk_mem_image_iff (u : EscapingQuotient x) :
    benderMk x u ∈ benderImage H x ↔ u ∈ escapingImage H x := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr hq.bar_mem_image)]

theorem exists_involution_mem_image_ne_bar :
    ∃ u ∈ escapingImage H x, orderOf u = 2 ∧ u ≠ escapingBar x := by
  obtain ⟨U, hUH, -⟩ := hq.sylow
  have hU : 2 ≤ CFSG.Open.pRank 2 (U : Subgroup (EscapingQuotient x)) := by
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq]
    have := hq.rank
    omega
  obtain ⟨a, haU, b, hbU, ha, hb, hab, -⟩ := exists_commuting_involutions_of_two_le_pRank hU
  by_cases hax : a = escapingBar x
  · exact ⟨b, hUH hbU, hb, fun h => hab (hax.trans h.symm)⟩
  · exact ⟨a, hUH haU, ha, hax⟩

theorem benderImage_isStronglyEmbedded (hsq : ∀ w : EscapingQuotient x, w ^ 2 ≠ escapingBar x) :
    BenderSuzuki.IsStronglyEmbedded (benderImage H x) := by
  refine ⟨fun htop => hq.image_ne_top (eq_top_iff.mpr fun u _ =>
    (hq.benderMk_mem_image_iff u).mp (htop ▸ Subgroup.mem_top _)), ?_, ?_⟩
  · obtain ⟨u, huH, hu, hux⟩ := hq.exists_involution_mem_image_ne_bar
    exact ⟨benderMk x u, Subgroup.mem_map_of_mem _ huH, isInvolution_benderMk hq.order hu hux⟩
  · intro g hg y hyB hyconj hyinv
    obtain ⟨u, rfl, hu, hux⟩ := exists_involution_lift_benderMk hq.order hsq hyinv
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ g
    have hm : m ∉ escapingImage H x := fun h => hg ((hq.benderMk_mem_image_iff m).mpr h)
    have huH := (hq.benderMk_mem_image_iff u).mp hyB
    rw [mem_rightConjugate_iff_conj_mem, ← map_mul, ← map_inv, ← map_mul,
      hq.benderMk_mem_image_iff] at hyconj
    exact hux (hq.eq_bar_of_conj_mem hm huH hyconj hu)

theorem benderQuotient_twoRankAtLeastTwo : TwoRankAtLeastTwo (BenderQuotient x) := by
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (by decide : 1 < 2) (⊤ : Subgroup (EscapingQuotient x))
  have h8 : 8 ≤ Nat.card E := by
    rw [hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup (EscapingQuotient x)) :=
        Nat.pow_le_pow_right (by norm_num) hq.rank
  set V := E.map (benderMk x)
  set f := (benderMk x).domRestrict E
  have hrange : f.range = V := MonoidHom.domRestrict_range E (benderMk x)
  have hker : Nat.card f.ker ≤ 2 := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    calc Nat.card ((Subgroup.zpowers (escapingBar x)).subgroupOf E)
        = Nat.card (Subgroup.zpowers (escapingBar x) ⊓ E : Subgroup (EscapingQuotient x)) := by
          rw [← Subgroup.subgroupOf_map_subtype,
            Subgroup.card_map_of_injective (Subgroup.subtype_injective E)]
      _ ≤ Nat.card (Subgroup.zpowers (escapingBar x)) := Subgroup.card_le_of_le inf_le_left
      _ = 2 := by rw [Nat.card_zpowers, hq.bar_order]
  have hmul := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange] at hmul
  have hV : 4 ≤ Nat.card V := by nlinarith
  exact twoRankAtLeastTwo_of_injective V.subtype V.subtype_injective
    (twoRankAtLeastTwo_of_elementary_card_ge_four V (CFSG.SectionRank.isElemAbelian_map hE _) hV)

theorem benderQuotient_normal_odd_eq_bot {N : Subgroup (BenderQuotient x)} [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  have h2 : IsPGroup 2 (N.comap (benderMk x)) := by
    refine isPGroup_two_of_normal_of_twoElements_commute hq.oddCore_eq_bot ?_
    intro p hp k hk m _
    rcases eq_one_or_eq_of_mem_zpowers hq.bar_order (mem_zpowers_of_comap_odd hN hp hk) with
      h | h
    · rw [h]
      exact Commute.one_left m
    · rw [h]
      exact (commute_escapingBar m).symm
  refine eq_bot_iff.mpr fun n hn => ?_
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective _ n
  obtain ⟨k, hk⟩ := h2 ⟨p, hn⟩
  have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact Subgroup.mem_bot.mpr (eq_one_of_pow_two_pow_eq_one_of_odd hN hn
    (by rw [← map_pow, hk', map_one]))

theorem exists_benderQuotient_normal_simpleBender
    (hsq : ∀ w : EscapingQuotient x, w ^ 2 ≠ escapingBar x) :
    ∃ N : Subgroup (BenderQuotient x), N.Normal ∧ Odd N.index ∧ IsSimpleBenderGroup N := by
  have hSE := hq.benderImage_isStronglyEmbedded hsq
  rcases theorem_SE _ hSE with hlow | hB
  · exact absurd (twoRankAtLeastTwo_involutionCore_iff.mpr hq.benderQuotient_twoRankAtLeastTwo)
      hlow
  · set L := involutionCore (BenderQuotient x)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hO : twoPrimeCore L = ⊥ := by
      have : (twoPrimeCore L).Characteristic := by
        simpa [twoPrimeCore] using (pPrimeCore_characteristic (p := 2) (G := L))
      have : ((twoPrimeCore L).map L.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
      have hodd : Odd (Nat.card ((twoPrimeCore L).map L.subtype)) := by
        rw [Subgroup.card_map_of_injective L.subtype_injective]
        exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := L))
      exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp
        (hq.benderQuotient_normal_odd_eq_bot hodd)
    refine ⟨L, inferInstance, hSE.involutionCore_index_odd_of_bender hB, ?_⟩
    exact hB.1.map_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hO).trans
      QuotientGroup.quotientBot)

theorem benderImage_fusionStronglyEmbedded
    (hsq : ∀ w : EscapingQuotient x, w ^ 2 ≠ escapingBar x) :
    fusionStronglyEmbedded (benderImage H x) :=
  fusionStronglyEmbedded.of_native (hq.benderImage_isStronglyEmbedded hsq)

theorem benderQuotient_normal_series
    (hsq : ∀ w : EscapingQuotient x, w ^ 2 ≠ escapingBar x) :
    ∃ (N₁ N₂ : Subgroup (BenderQuotient x)) (_ : N₁.Normal) (_ : N₂.Normal)
      (_ : (N₁.subgroupOf N₂).Normal), N₁ = ⊥ ∧ N₁ ≤ N₂ ∧ Odd (Nat.card N₁) ∧ Odd N₂.index ∧
        fusionIsBenderGroup (N₂ ⧸ N₁.subgroupOf N₂) := by
  obtain ⟨N, hN, hNodd, hNB⟩ := hq.exists_benderQuotient_normal_simpleBender hsq
  refine ⟨⊥, N, inferInstance, hN, inferInstance, rfl, bot_le, by simp, hNodd, ?_⟩
  exact fusionIsBenderGroup_of_isSimpleBenderGroup (hNB.map_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf N)).trans
      QuotientGroup.quotientBot).symm)

end EscapingQuotientData

end CFSG.ProperTwoGeneratedCore.Assembly
