module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEnd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur

public section

namespace CFSG.ComponentClassification.GrSLit.L34GM

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem pRank_two_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) : pRank 2 X ≤ pRank 2 Y := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact SectionRank.pRank_top_le_of_injective (by norm_num) f hf

theorem card_fusionZStar_eq (K : Type*) [Group K] [Finite K] :
    Nat.card ↥(Open.fusionZStar K) =
      Nat.card ↥(pPrimeCore 2 K) * Nat.card ↥(center (K ⧸ pPrimeCore 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 K)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  rw [HarrisLit.card_fusionZStar_of_surjective _ (QuotientGroup.mk'_surjective _) hker,
    QuotientGroup.ker_mk',
    HarrisLit.fusionZStar_eq_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)]

variable {G : Type} [Group G] [Finite G]

theorem exists_center_param {J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) :
    ∃ A B : Jhat J, A ∈ center (Jhat J) ∧ B ∈ center (Jhat J) ∧ A ^ 4 = 1 ∧ B ^ 4 = 1 ∧
      (∀ z ∈ center (Jhat J), ∃ x : Fin 4 × Fin 4, z = A ^ x.1.val * B ^ x.2.val) ∧
      Nat.card (Jhat J) = 20160 * Nat.card (center (Jhat J)) := by
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls⟩ := exists_setting hJ hL
  obtain ⟨hAZ, hBZ, hA4, hB4⟩ := lam_z_facts (hqker ▸ le_refl _) hl
  refine ⟨l z₁, l z₂, hAZ, hBZ, hA4, hB4, fun z hz => ?_, ?_⟩
  · rw [← hqker] at hz
    obtain ⟨i, j, rfl⟩ := (mem_ker_iff hl hls h3).mp hz
    refine ⟨(⟨i % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    change l z₁ ^ i * l z₂ ^ j = l z₁ ^ (i % 4) * l z₂ ^ (j % 4)
    rw [← pow_eq_pow_mod i hA4, ← pow_eq_pow_mod j hB4]
  · have hr : q.range = S := by
      ext s
      rw [MonoidHom.mem_range]
      exact ⟨fun ⟨e, he⟩ => he ▸ hqS e, fun hs => hqsurj s hs⟩
    rw [← Subgroup.card_ker_mul_card_range q, hr, card_S, hqker, mul_comm]

theorem card_center_le {J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) : Nat.card (center (Jhat J)) ≤ 16 := by
  obtain ⟨A, B, hAZ, hBZ, -, -, hpar, -⟩ := exists_center_param hJ hL
  let f : Fin 4 × Fin 4 → center (Jhat J) :=
    fun x => ⟨A ^ x.1.val * B ^ x.2.val, mul_mem (pow_mem hAZ _) (pow_mem hBZ _)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := hpar z hz
    exact ⟨x, rfl⟩
  calc Nat.card (center (Jhat J)) ≤ Nat.card (Fin 4 × Fin 4) :=
        Nat.card_le_card_of_surjective f hsurj
    _ = 16 := by rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem index_le {J : Subgroup G} (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) :
    (pPrimeCore 2 ↥J).index ≤ 322560 := by
  obtain ⟨-, -, -, -, -, -, -, hcard⟩ := exists_center_param hJ hL
  rw [Subgroup.index_eq_card, show Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = Nat.card (Jhat J) from rfl,
    hcard]
  have := card_center_le hJ hL
  omega

theorem card_center_of_index {J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) :
    (pPrimeCore 2 ↥J).index = 322560 ↔ Nat.card (center (Jhat J)) = 16 := by
  obtain ⟨-, -, -, -, -, -, -, hcard⟩ := exists_center_param hJ hL
  rw [Subgroup.index_eq_card, show Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = Nat.card (Jhat J) from rfl,
    hcard]
  omega

theorem exists_pair_center {J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (h16 : Nat.card (center (Jhat J)) = 16) :
    ∃ u v : Jhat J, u ∈ center (Jhat J) ∧ v ∈ center (Jhat J) ∧ u * u = 1 ∧ v * v = 1 ∧
      u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  obtain ⟨A, B, hAZ, hBZ, hA4, hB4, hpar, -⟩ := exists_center_param hJ hL
  let f : Fin 4 × Fin 4 → center (Jhat J) :=
    fun x => ⟨A ^ x.1.val * B ^ x.2.val, mul_mem (pow_mem hAZ _) (pow_mem hBZ _)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := hpar z hz
    exact ⟨x, rfl⟩
  have hinj : Function.Injective f := by
    have hc : Nat.card (Fin 4 × Fin 4) = Nat.card (center (Jhat J)) := by
      rw [h16, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact (Function.Surjective.bijective_of_nat_card_le hsurj hc.le).1
  have hval : ∀ x y : Fin 4 × Fin 4, f x = f y → x = y := fun x y h => hinj h
  have e20 : f (2, 0) = ⟨A ^ 2, pow_mem hAZ 2⟩ := Subtype.ext (by simp [f])
  have e02 : f (0, 2) = ⟨B ^ 2, pow_mem hBZ 2⟩ := Subtype.ext (by simp [f])
  have e00 : f (0, 0) = 1 := Subtype.ext (by simp [f])
  refine ⟨A ^ 2, B ^ 2, pow_mem hAZ 2, pow_mem hBZ 2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← pow_add, show 2 + 2 = 4 by norm_num, hA4]
  · rw [← pow_add, show 2 + 2 = 4 by norm_num, hB4]
  · intro h
    have : f (2, 0) = f (0, 0) := by rw [e20, e00]; exact Subtype.ext h
    exact absurd (hval _ _ this) (by decide)
  · intro h
    have : f (0, 2) = f (0, 0) := by rw [e02, e00]; exact Subtype.ext h
    exact absurd (hval _ _ this) (by decide)
  · intro h
    have : f (2, 0) = f (0, 2) := by rw [e20, e02]; exact Subtype.ext h
    exact absurd (hval _ _ this) (by decide)

section Lift

theorem not_two_dvd_card_ker_jq (J : Subgroup G) : ¬ 2 ∣ Nat.card (jq J).ker := by
  rw [QuotientGroup.ker_mk']
  exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card

theorem fusionZStar_eq_comap (J : Subgroup G) :
    Open.fusionZStar ↥J = (center (Jhat J)).comap (jq J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← HarrisLit.fusionZStar_eq_center_of_pPrimeCore_eq_bot
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)]
  exact (GSThmB.OddQuot.comap_fusionZStar_of_surjective _ (QuotientGroup.mk'_surjective _)
    (not_two_dvd_card_ker_jq J)).symm

theorem mem_fusionZStar_iff (J : Subgroup G) (x : ↥J) :
    x ∈ Open.fusionZStar ↥J ↔ jq J x ∈ center (Jhat J) := by
  rw [fusionZStar_eq_comap J]
  exact Iff.rfl

noncomputable def centerMap (J : Subgroup G) : ↥(Open.fusionZStar ↥J) →* ↥(center (Jhat J)) :=
  ((jq J).comp (Open.fusionZStar ↥J).subtype).codRestrict _ fun u =>
    (mem_fusionZStar_iff J u).mp u.2

theorem centerMap_surjective (J : Subgroup G) : Function.Surjective (centerMap J) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  exact ⟨⟨x, (mem_fusionZStar_iff J x).mpr hz⟩, rfl⟩

theorem not_two_dvd_card_ker_centerMap (J : Subgroup G) :
    ¬ 2 ∣ Nat.card (centerMap J).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.card_ker_mul_card_range (centerMap J)
  rw [MonoidHom.range_eq_top_of_surjective _ (centerMap_surjective J), card_top,
    HarrisLit.card_fusionZStar_of_surjective _ (QuotientGroup.mk'_surjective _)
      (not_two_dvd_card_ker_jq J),
    HarrisLit.fusionZStar_eq_center_of_pPrimeCore_eq_bot
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2)] at h1
  rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos h1]
  exact not_two_dvd_card_ker_jq J

theorem pRank_center_le (J : Subgroup G) :
    pRank 2 ↥(center (Jhat J)) ≤ pRank 2 ↥(Open.fusionZStar ↥J) := by
  have hq := GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
    (centerMap J).ker (not_two_dvd_card_ker_centerMap J)
  have e := QuotientGroup.quotientKerEquivOfSurjective (centerMap J) (centerMap_surjective J)
  exact (pRank_two_le_of_injective e.symm.toMonoidHom e.symm.injective).trans hq.le

end Lift

theorem two_le_pRank_of_index {J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hidx : (pPrimeCore 2 ↥J).index = 322560) :
    2 ≤ pRank 2 ↥(Open.fusionZStar ↥J) := by
  obtain ⟨u, v, hu, hv, huu, hvv, hu1, hv1, huv⟩ :=
    exists_pair_center hJ hL ((card_center_of_index hJ hL).mp hidx)
  exact (HeEnd.two_le_pRank_of_pair hu hv huu hvv hu1 hv1 huv (mem_center_iff.mp hv u)).trans
    (pRank_center_le J)

end CFSG.ComponentClassification.GrSLit.L34GM
