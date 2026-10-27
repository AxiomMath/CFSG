module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CharacteristicCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.OddNormalQuotient
public import CFSG.GroupTheory.Fitting.CharacteristicP

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem two_rank_eq_odd_normal_quotient
    (R : Subgroup G) [R.Normal] (hRodd : Odd (Nat.card R)) :
    twoRank (G ⧸ R) = twoRank G := by
  change Open.pRank 2 (⊤ : Subgroup (G ⧸ R)) = Open.pRank 2 (⊤ : Subgroup G)
  apply (pRank_top_eq_of_coprime_kernel 2 Nat.prime_two (QuotientGroup.mk' R)
    (QuotientGroup.mk'_surjective R) ?_).symm
  rw [QuotientGroup.ker_mk']
  exact Nat.coprime_two_left.mpr hRodd

omit [Finite G] in
theorem central_involution_mem_two_core
    (t : G) (htcenter : t ∈ Subgroup.center G) (ht : orderOf t = 2) :
    t ∈ pCore 2 G := by
  have hnormal : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr htcenter)
  have htwo : IsPGroup 2 (Subgroup.zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht]
    norm_num)
  have hle : Subgroup.zpowers t ≤ pCore 2 G := le_sSup ⟨hnormal, htwo⟩
  exact hle (Subgroup.mem_zpowers t)

omit [Finite G] in
theorem central_involution_odd_quotient
    (R : Subgroup G) [R.Normal] (hRodd : Odd (Nat.card R))
    (t : G) (htcenter : t ∈ Subgroup.center G) (ht : orderOf t = 2) :
    QuotientGroup.mk' R t ∈ Subgroup.center (G ⧸ R) ∧
      orderOf (QuotientGroup.mk' R t) = 2 := by
  let pi := QuotientGroup.mk' R
  have hcenter : pi t ∈ Subgroup.center (G ⧸ R) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp htcenter g]
  have htR : t ∉ R := by
    intro hmem
    have hdiv := orderOf_dvd_natCard (⟨t, hmem⟩ : R)
    rw [← orderOf_submonoid, ht] at hdiv
    exact hRodd.not_two_dvd_nat hdiv
  have hne : pi t ≠ 1 := by
    intro heq
    exact htR ((QuotientGroup.eq_one_iff _).mp heq)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hcenter, orderOf_eq_prime ?_ hne⟩
  rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]

theorem one_le_two_rank_of_involution_mem
    (Q : Subgroup G) (t : G) (htQ : t ∈ Q) (ht : orderOf t = 2) :
    1 ≤ Open.pRank 2 Q := by
  let E := Subgroup.zpowers t
  have helementary : IsElemAbelian 2 E := by
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨power, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← ht]
    exact zpow_pow_orderOf
  apply le_csSup (pRank_set_bddAbove 2 (by decide) Q)
  refine ⟨E, Subgroup.zpowers_le.mpr htQ, helementary, ?_⟩
  rw [Nat.card_zpowers, ht]
  norm_num

theorem central_involution_proper_core_local_structure
    (hrank : 3 ≤ twoRank G) (t : G) (htcenter : t ∈ Subgroup.center G)
    (ht : orderOf t = 2) (S : Sylow 2 G)
    (hproper : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    let R := pPrimeCore 2 G
    let pi := QuotientGroup.mk' R
    let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective R)
    let K := properTwoGenCoreGamma (S : Subgroup G) 2
    let Kbar := properTwoGenCoreGamma (Sbar : Subgroup (G ⧸ R)) 2
    R ≤ K ∧ K.map pi = Kbar ∧ Kbar < ⊤ ∧
      twoRank (G ⧸ R) = twoRank G ∧ 3 ≤ twoRank (G ⧸ R) ∧
      pPrimeCore 2 (G ⧸ R) = ⊥ ∧
      pi t ∈ Subgroup.center (G ⧸ R) ∧ orderOf (pi t) = 2 ∧
      pi t ∈ pCore 2 (G ⧸ R) ∧ Open.pRank 2 (pCore 2 (G ⧸ R)) = 1 ∧
      ¬ IsCharacteristicP 2 (G ⧸ R) ∧ layer (G ⧸ R) ≠ ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R := pPrimeCore 2 G
  let pi := QuotientGroup.mk' R
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective R)
  let K := properTwoGenCoreGamma (S : Subgroup G) 2
  let Kbar := properTwoGenCoreGamma (Sbar : Subgroup (G ⧸ R)) 2
  have hRodd : Odd (Nat.card R) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))
  have hSrank : 3 ≤ Open.pRank 2 (S : Subgroup G) := by
    rwa [sylow_two_rank_eq]
  have hRle : R ≤ K := odd_normal_le_full_core S hSrank R hRodd
  have himage : K.map pi = Kbar := by
    change (properTwoGenCoreGamma (S : Subgroup G) 2).map (QuotientGroup.mk' R) =
      properTwoGenCoreGamma (Sbar : Subgroup (G ⧸ R)) 2
    rw [Sylow.coe_mapSurjective]
    exact gamma_image_odd_normal_quotient S R hRodd 2
  have hKbar : Kbar ≠ ⊤ := by
    change properTwoGenCoreGamma (Sbar : Subgroup (G ⧸ R)) 2 ≠ ⊤
    rw [Sylow.coe_mapSurjective]
    exact fun htop => hproper
      ((full_core_eq_top_iff_odd_normal_quotient S hSrank R hRodd).mpr htop)
  have hrankEq : twoRank (G ⧸ R) = twoRank G :=
    two_rank_eq_odd_normal_quotient R hRodd
  have hbarRank : 3 ≤ twoRank (G ⧸ R) := hrankEq ▸ hrank
  have hbarOddCore : pPrimeCore 2 (G ⧸ R) = ⊥ :=
    pPrimeCore_quotient_pPrimeCore_eq_bot 2
  obtain ⟨htbarCenter, htbarOrder⟩ :=
    central_involution_odd_quotient R hRodd t htcenter ht
  have htbarCore : pi t ∈ pCore 2 (G ⧸ R) :=
    central_involution_mem_two_core (pi t) htbarCenter htbarOrder
  have hcoreRank : Open.pRank 2 (pCore 2 (G ⧸ R)) = 1 :=
    le_antisymm (two_core_rank_le_one_of_proper_full_core Sbar hKbar)
      (one_le_two_rank_of_involution_mem (pCore 2 (G ⧸ R)) (pi t) htbarCore htbarOrder)
  have hnotChar : ¬ IsCharacteristicP 2 (G ⧸ R) := fun hchar =>
    hKbar (characteristic_two_rank_three_full_core hchar hbarRank Sbar)
  have hlayer : layer (G ⧸ R) ≠ ⊥ := fun htrivial =>
    hnotChar (isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot
      (G ⧸ R) 2 hbarOddCore htrivial)
  exact ⟨hRle, himage, lt_top_iff_ne_top.mpr hKbar, hrankEq, hbarRank,
    hbarOddCore, htbarCenter, htbarOrder, htbarCore, hcoreRank, hnotChar, hlayer⟩

end CFSG.ProperTwoGeneratedCore
