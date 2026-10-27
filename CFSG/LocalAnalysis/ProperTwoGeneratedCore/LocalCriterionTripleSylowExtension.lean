module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylow
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylowContainment

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

open CFSG.BenderSuzuki.External

universe u

variable {K : Type u} [Group K] [Finite K]

theorem invariant_two_subgroup_extends
    (B X : Subgroup K) [B.Normal] (t : K) (ht : orderOf t = 2)
    (hXB : X ≤ B) (hX : IsPGroup 2 X)
    (hXnorm : t ∈ Subgroup.normalizer (X : Set K)) :
    ∃ P : Sylow 2 B, X ≤ (P : Subgroup B).map B.subtype ∧
      t ∈ Subgroup.normalizer (((P : Subgroup B).map B.subtype : Subgroup K) : Set K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : IsPGroup 2 (X ⊔ Subgroup.zpowers t : Subgroup K) :=
    hX.to_sup_of_normal_left' (involution_cyclic_actor_is_two_group t ht)
      (Subgroup.zpowers_le.mpr hXnorm)
  obtain ⟨R, hR⟩ := htwo.exists_le_sylow
  have htR : t ∈ (R : Subgroup K) := hR
    ((show Subgroup.zpowers t ≤ X ⊔ Subgroup.zpowers t from le_sup_right)
      (Subgroup.mem_zpowers t))
  let P := hallSylowSubgroupOfNormal R B
  have himage : (P : Subgroup B).map B.subtype = (R : Subgroup K) ⊓ B := by
    rw [hallSylowSubgroupOfNormal_coe, Subgroup.comap_subtype,
      Subgroup.subgroupOf_map_subtype]
  refine ⟨P, ?_, ?_⟩
  · rw [himage]
    exact le_inf (le_sup_left.trans hR) hXB
  · rw [himage]
    apply Subgroup.mem_normalizer_iff.mpr
    intro a
    constructor
    · rintro ⟨haR, haB⟩
      exact ⟨(R : Subgroup K).mul_mem ((R : Subgroup K).mul_mem htR haR)
        ((R : Subgroup K).inv_mem htR), (inferInstance : B.Normal).conj_mem a haB t⟩
    · rintro ⟨haR, haB⟩
      have hpreR := (R : Subgroup K).mul_mem
        ((R : Subgroup K).mul_mem ((R : Subgroup K).inv_mem htR) haR) htR
      have hpreB := (inferInstance : B.Normal).conj_mem (t * a * t⁻¹) haB t⁻¹
      constructor
      · change a ∈ (R : Subgroup K)
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
          inv_mul_cancel, mul_one] using hpreR
      · change a ∈ B
        simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
          inv_mul_cancel, mul_one] using hpreB

omit [Finite K] in
theorem quotient_sylow_preimage_eq
    (B J : Subgroup K) [J.Normal] (p : ℕ) (P : Sylow p B) :
    (((P : Subgroup B).map B.subtype).map (QuotientGroup.mk' J)).comap
        (QuotientGroup.mk' J) = (P : Subgroup B).map B.subtype ⊔ J := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem invariant_odd_subgroup_extends
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (B J X : Subgroup K) [J.Normal] (t : K) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J)) (hJB : J ≤ B)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J))
    (hXB : X ≤ B) (hX : IsPGroup p X)
    (hXnorm : t ∈ Subgroup.normalizer (X : Set K)) :
    ∃ P : Sylow p B, X ≤ (P : Subgroup B).map B.subtype ∧
      t ∈ Subgroup.normalizer (((P : Subgroup B).map B.subtype : Subgroup K) : Set K) := by
  have hXBp : IsPGroup p (X.subgroupOf B) :=
    hX.of_injective (Subgroup.subgroupOfEquivOfLe hXB).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXB).injective
  obtain ⟨P₀, hXP₀⟩ := hXBp.exists_le_sylow
  have hXP₀ambient : X ≤ (P₀ : Subgroup B).map B.subtype := by
    have hmap := Subgroup.map_mono (f := B.subtype) hXP₀
    rw [Subgroup.map_subgroupOf_eq_of_le hXB] at hmap
    exact hmap
  let Y := (P₀ : Subgroup B).map B.subtype ⊔ J
  have hXY : X ≤ Y := hXP₀ambient.trans le_sup_left
  have hYB : Y ≤ B := sup_le (Subgroup.map_subtype_le _) hJB
  have hYodd : Odd (Nat.card Y) :=
    odd_sylow_times_odd_normal_subgroup p hp hpodd B J P₀ hJodd
  have hYnorm := odd_central_quotient_subgroup_normalized J Y t le_sup_right hcentral
  obtain ⟨R, hXR, hRnorm⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_containing_normalized_pSubgroup
      2 Nat.prime_two p hp (Subgroup.zpowers t) Y X
      (involution_cyclic_actor_is_two_group t ht) hYodd.not_two_dvd_nat
      hYnorm hXY hX (Subgroup.zpowers_le.mpr hXnorm)
  have hindex : ¬ p ∣ Y.relIndex B :=
    sylow_overgroup_relIndex_prime_to p hp B Y P₀ le_sup_left
  obtain ⟨P, hPimage⟩ := sylow_extension_same_ambient_image p hp B Y hYB hindex R
  refine ⟨P, ?_, ?_⟩
  · rw [hPimage]
    exact hXR
  · rw [hPimage]
    exact hRnorm (Subgroup.mem_zpowers t)

theorem invariant_subgroup_extends
    (p : ℕ) (hp : p.Prime) (B J X : Subgroup K) [B.Normal] [J.Normal]
    (t : K) (ht : orderOf t = 2) (hJodd : Odd (Nat.card J)) (hJB : J ≤ B)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J))
    (hXB : X ≤ B) (hX : IsPGroup p X)
    (hXnorm : t ∈ Subgroup.normalizer (X : Set K)) :
    ∃ P : Sylow p B, X ≤ (P : Subgroup B).map B.subtype ∧
      t ∈ Subgroup.normalizer (((P : Subgroup B).map B.subtype : Subgroup K) : Set K) := by
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · exact invariant_two_subgroup_extends B X t ht hXB hX hXnorm
  · exact invariant_odd_subgroup_extends p hp hpodd B J X t ht hJodd hJB
      hcentral hXB hX hXnorm

end CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
