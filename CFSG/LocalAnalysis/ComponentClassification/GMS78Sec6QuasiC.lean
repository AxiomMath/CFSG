module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6MainC
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6KFacts

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.ComponentClassification.RankTwoStandard CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_le_standardComponentOddCore {K : Subgroup G} (hKo : Odd (Nat.card K)) :
    (K ⊓ centralizer (K : Set G)).subgroupOf (centralizer (K : Set G)) ≤
      standardComponentOddCore (centralizer (K : Set G)) := by
  set G₁ := centralizer (K : Set G)
  refine le_standardComponentOddCore' ⟨fun n hn g => ?_⟩ ?_
  · have hn' : ((n : G₁) : G) ∈ K ⊓ G₁ := mem_subgroupOf.mp hn
    have hng : ((n : G₁) : G) * g = g * n := (mem_centralizer_iff.mp g.2) n (mem_inf.mp hn').1
    have he : ((g * n * g⁻¹ : G₁) : G) = n := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hng, mul_inv_cancel_right]
    rw [mem_subgroupOf, he]
    exact hn'
  · rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : K ⊓ G₁ ≤ G₁)).toEquiv]
    exact hKo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem gms61QuasisimpleC : GMS61QuasisimpleC := by
  intro G _ _ L T K f hf he h3 hKL hKo hKH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he
  obtain ⟨hZK, hdec, -, -, -, -, ⟨eX⟩, -⟩ := u3K_facts h3 hf e hKL hKo hKH
  have h4 : ∃ s : Finset (GaloisField 2 f), s.card = 4 := by
    have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    have hc : 4 ≤ (Finset.univ : Finset (GaloisField 2 f)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
      exact le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hc
    exact ⟨s, hs⟩
  set G₁ := centralizer (K : Set G)
  set X₀ := u3X₀ L K
  have hX₀G₁ : X₀ ≤ G₁ := by
    refine (commutator_le).mpr fun x hx y hy => ?_
    exact mul_mem (mul_mem (mul_mem (mem_inf.mp hx).2 (mem_inf.mp hy).2)
      (inv_mem (mem_inf.mp hx).2)) (inv_mem (mem_inf.mp hy).2)
  set X₀' : Subgroup G₁ := X₀.subgroupOf G₁
  have eX' : rankTwoQuot X₀' ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
    (quotCenterCongr (subgroupOfEquivOfLe hX₀G₁)).trans eX
  have hsimp : IsSimpleGroup (rankTwoQuot X₀') := by
    have := u3_isSimpleGroup_SL2 (GaloisField 2 f) h4
    exact eX'.isSimpleGroup
  have hcen : center (rankTwoQuot X₀') = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eX' z ∈ center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := eX'.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) w]
    rw [u3_center_SL2_eq_bot, mem_bot] at h1
    rw [mem_bot]
    exact eX'.injective (h1.trans (map_one eX').symm)
  have heven : Even (Nat.card (rankTwoQuot X₀')) := by
    rw [Nat.card_congr eX'.toEquiv]
    exact u3_even_card_SL2 _
  obtain ⟨eq⟩ := nonempty_quotCenter_map_equiv (N := standardComponentOddCore G₁)
    odd_card_standardComponentOddCore' hsimp hcen heven
  have hZO := inf_centralizer_le_standardComponentOddCore hKo
  have hX₀X₀ : ⁅X₀, X₀⁆ = (⁅X₀', X₀'⁆).map G₁.subtype := by
    rw [map_commutator, subgroupOf_map_subtype, inf_eq_left.mpr hX₀G₁]
  have hperf : ⁅oddQuotImageC K X₀, oddQuotImageC K X₀⁆ = oddQuotImageC K X₀ := by
    apply le_antisymm
    · exact commutator_le.mpr fun x hx y hy =>
        mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc, z, hz, hxe⟩ := hdec (x : G) hx
      have hzK : (z : G) ∈ K := hZK z hz
      have hzG₁ : (z : G) ∈ G₁ := mem_centralizer_iff.mpr fun k hk =>
        congrArg Subtype.val (mem_center_iff.mp hz ⟨k, hKL hk⟩)
      rw [hX₀X₀] at hc
      obtain ⟨c', hc', hc'e⟩ := hc
      have hc'e' : (c' : G) = c := hc'e
      have hxe' : x = c' * ⟨(z : G), hzG₁⟩ := Subtype.ext (by
        rw [Subgroup.coe_mul, hc'e', ← hxe])
      rw [hxe', map_mul]
      have hz1 : QuotientGroup.mk' (standardComponentOddCore G₁)
          (⟨(z : G), hzG₁⟩ : G₁) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hZO (mem_subgroupOf.mpr (mem_inf.mpr ⟨hzK, hzG₁⟩))
      rw [hz1, mul_one, ← map_commutator]
      exact ⟨c', hc', rfl⟩
  refine ⟨Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf), ?_⟩
  have := hsimp
  exact eq.symm.isSimpleGroup

end CFSG.ComponentClassification.GMS78
