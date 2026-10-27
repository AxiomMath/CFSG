
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGenBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEights
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowPosition

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] {J P : Subgroup G}

theorem l34TwoEightsFact :
    L34TwoEightsFact := by
  intro G _ _ J P hJ hL hP
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨E₁, E₂, h1, h2, hE1, hE2, hne⟩ := hQ.exists_eights
  have h1' : E₁ ≤ T0.comap q := h1.trans (comap_mono U1_le_T0)
  have h2' : E₂ ≤ T0.comap q := h2.trans (comap_mono U2_le_T0)
  refine ⟨pullP J P hP.1 E₁, pullP J P hP.1 E₂, pullP_le _, pullP_le _,
    ⟨isElemTwo_pullP hP2 hE1.1, by rw [card_pullP hP2 hT h1', hE1.2]⟩,
    ⟨isElemTwo_pullP hP2 hE2.1, by rw [card_pullP hP2 hT h2', hE2.2]⟩, fun heq => hne ?_⟩
  exact le_antisymm (le_of_pullP_le hT h1' heq.le) (le_of_pullP_le hT h2' heq.ge)

theorem T0_le_B0 :
    T0 ≤ B0 := fun _ ht =>
  normalizer_T0_le (T0_le_S ht) fun _ ht' => T0.mul_mem (T0.mul_mem ht ht') (T0.inv_mem ht)

theorem T0_le_normalizer_U1 :
    T0 ≤ normalizer (U1 : Set (Equiv.Perm (Fin 42))) :=
  T0_le_B0.trans (B0_le_P1_P2.1.trans P1_le_normalizer_U1)

variable {q : Jhat J →* Equiv.Perm (Fin 42)}

theorem l34ParabolicGenerationFact :
    L34ParabolicGenerationFact := by
  intro G _ _ J P hJ hL hP
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨E₁, E₂, h1, h2, hE1, hE2, -⟩ := hQ.exists_eights
  set T₁ := pullP J P hP.1 (U1.comap q) with hT₁
  set T₂ := pullP J P hP.1 (U2.comap q) with hT₂
  refine ⟨T₁, T₂, pullP_le _, pullP_le _,
    ⟨pullP J P hP.1 E₁, pullP_mono h1, isElemTwo_pullP hP2 hE1.1,
      by rw [card_pullP hP2 hT (h1.trans (comap_mono U1_le_T0)), hE1.2]⟩,
    ⟨pullP J P hP.1 E₂, pullP_mono h2, isElemTwo_pullP hP2 hE2.1,
      by rw [card_pullP hP2 hT (h2.trans (comap_mono U2_le_T0)), hE2.2]⟩, ?_⟩
  set H := (J ⊓ normalizer (T₁ : Set G)) ⊔ (J ⊓ normalizer (T₂ : Set G)) with hH
  have hHJ : H ≤ J := sup_le inf_le_left inf_le_left
  have hPH : P ≤ H := fun p hp =>
    mem_sup_left ⟨hP.1 hp, le_normalizer_pullP hP hT T0_le_normalizer_U1 hp⟩
  have hlift : ∀ {U : Subgroup (Equiv.Perm (Fin 42))}, U ≤ T0 →
      J ⊓ normalizer (pullP J P hP.1 (U.comap q) : Set G) ≤ H →
      ∀ s ∈ S, s ∈ normalizer (U : Set (Equiv.Perm (Fin 42))) →
        ∃ n, ∃ hn : n ∈ J, n ∈ H ∧ q (jq J ⟨n, hn⟩) = s := by
    intro U hUT hUH s hs hsU
    obtain ⟨n, hnJ, hnN, hnU⟩ := exists_lift_normalizer hP hqsurj hT hUT hs hsU
    obtain ⟨e, he⟩ := hqsurj _ (T0_le_S (hUT hnU))
    obtain ⟨p, hpP, hpJ, hpe⟩ := (hT e).1 (by rw [he]; exact hUT hnU)
    have hpe' : q (jq J ⟨p, hpJ⟩) = q (jq J ⟨n, hnJ⟩) * s⁻¹ := by rw [hpe, he]
    refine ⟨p⁻¹ * n, J.mul_mem (J.inv_mem hpJ) hnJ,
      H.mul_mem (H.inv_mem (hPH hpP)) (hUH ⟨hnJ, hnN⟩), ?_⟩
    have e : (⟨p⁻¹ * n, J.mul_mem (J.inv_mem hpJ) hnJ⟩ : J) = (⟨p, hpJ⟩ : J)⁻¹ * ⟨n, hnJ⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hpe', mul_inv_rev, inv_inv, mul_assoc,
      inv_mul_cancel, mul_one]
  set Q : Subgroup (Equiv.Perm (Fin 42)) := (H.subgroupOf J).map (q.comp (jq J)) with hQd
  have hmemQ : ∀ s, (∃ n, ∃ hn : n ∈ J, n ∈ H ∧ q (jq J ⟨n, hn⟩) = s) → s ∈ Q := by
    rintro s ⟨n, hnJ, hnH, rfl⟩
    exact ⟨⟨n, hnJ⟩, mem_subgroupOf.mpr hnH, rfl⟩
  have hP1Q : P1 ≤ Q := fun s hs => hmemQ s (hlift U1_le_T0 le_sup_left s
    (closure_wordSet_le _ hs) (P1_le_normalizer_U1 hs))
  have hP2Q : P2 ≤ Q := fun s hs => hmemQ s (hlift U2_le_T0 le_sup_right s
    (closure_wordSet_le _ hs) (P2_le_normalizer_U2 hs))
  have hSQ : S ≤ Q := sup_P1_P2 ▸ sup_le hP1Q hP2Q
  intro j hj
  obtain ⟨⟨n, hnJ⟩, hnH, hns⟩ := hSQ (hqS (jq J ⟨j, hj⟩))
  have hnH' : n ∈ H := hnH
  have hz : jq J ((⟨n, hnJ⟩ : J)⁻¹ * ⟨j, hj⟩) ∈ center (Jhat J) := by
    rw [← hqker, MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv]
    have : q (jq J ⟨n, hnJ⟩) = q (jq J ⟨j, hj⟩) := hns
    rw [this, inv_mul_cancel]
  obtain ⟨z, hzP, hzJ, hzq⟩ := exists_mem_of_mem_center hP hz
  have ho : z⁻¹ * (n⁻¹ * j) ∈ oddIn J := by
    have hmem : z⁻¹ * (n⁻¹ * j) ∈ J := J.mul_mem (J.inv_mem hzJ) (J.mul_mem (J.inv_mem hnJ) hj)
    rw [mem_oddIn_iff hmem]
    have e : (⟨z⁻¹ * (n⁻¹ * j), hmem⟩ : J) = (⟨z, hzJ⟩ : J)⁻¹ * ((⟨n, hnJ⟩ : J)⁻¹ * ⟨j, hj⟩) :=
      rfl
    rw [e, map_mul, map_inv, hzq, inv_mul_cancel]
  have hH_le : H ≤ oddIn J ⊔ (J ⊓ normalizer (T₁ : Set G)) ⊔ (J ⊓ normalizer (T₂ : Set G)) :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hO_le : oddIn J ≤ oddIn J ⊔ (J ⊓ normalizer (T₁ : Set G)) ⊔
      (J ⊓ normalizer (T₂ : Set G)) := le_sup_left.trans le_sup_left
  have hj' : j = n * z * (z⁻¹ * (n⁻¹ * j)) := by group
  rw [hj']
  exact mul_mem (mul_mem (hH_le hnH') (hH_le (hPH hzP))) (hO_le ho)

end CFSG.ComponentClassification.GrSLit.L34Facts
