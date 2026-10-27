module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentral

variable {K : Type*} [Group K]

theorem quotient_center_restrict
    (R B : Subgroup K) [R.Normal] (t : B)
    (hcentral : QuotientGroup.mk' R (t : K) ∈ Subgroup.center (K ⧸ R)) :
    QuotientGroup.mk' (R.subgroupOf B) t ∈
      Subgroup.center (B ⧸ R.subgroupOf B) := by
  apply Subgroup.mem_center_iff.mpr
  intro q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  have hcomm := Subgroup.mem_center_iff.mp hcentral
    (QuotientGroup.mk (b : K) : K ⧸ R)
  have hkernel : ((b : K) * (t : K))⁻¹ * ((t : K) * (b : K)) ∈ R := by
    apply QuotientGroup.eq.mp
    simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul] using hcomm
  apply QuotientGroup.eq.mpr
  change ((b : K) * (t : K))⁻¹ * ((t : K) * (b : K)) ∈ R
  exact hkernel

theorem odd_card_restricted_kernel [Finite K]
    (R B : Subgroup K) (hRodd : Odd (Nat.card R)) :
    Odd (Nat.card (R.subgroupOf B)) := by
  have hodd : Odd (Nat.card (R ⊓ B : Subgroup K)) :=
    hRodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show R ⊓ B ≤ B from inf_le_right)).toEquiv] at hodd
  simpa only [Subgroup.inf_subgroupOf_right] using hodd

theorem central_odd_quotient_invariant_subgroup_sylow [Finite K]
    (R B : Subgroup K) [R.Normal] (hRodd : Odd (Nat.card R))
    (t : B) (ht : orderOf t = 2)
    (hcentral : QuotientGroup.mk' R (t : K) ∈ Subgroup.center (K ⧸ R))
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ∃ Q : Sylow p B,
      (t : K) ∈ Subgroup.normalizer
      (((Q : Subgroup B).map B.subtype : Subgroup K) : Set K) := by
  let : Fact p.Prime := ⟨hp⟩
  let J := R.subgroupOf B
  have hJodd : Odd (Nat.card J) := odd_card_restricted_kernel R B hRodd
  have hJcentral : QuotientGroup.mk' J t ∈ Subgroup.center (B ⧸ J) :=
    quotient_center_restrict R B t hcentral
  obtain ⟨Q, hQnorm⟩ := odd_central_quotient_invariant_odd_sylow_exists
    p hp hodd (⊤ : Subgroup B) J t ht hJodd le_top hJcentral
  let W : Subgroup B := (Q : Subgroup (⊤ : Subgroup B)).map (⊤ : Subgroup B).subtype
  have hWp : IsPGroup p W := Q.isPGroup'.map _
  have hWindex : ¬ p ∣ W.index := by
    rw [Subgroup.index_map_subtype, Subgroup.index_top, mul_one]
    exact Q.not_dvd_index
  let Q' := hWp.toSylow hWindex
  refine ⟨Q', ?_⟩
  change (t : K) ∈ Subgroup.normalizer ((W.map B.subtype : Subgroup K) : Set K)
  exact Subgroup.le_normalizer_map B.subtype
    (Subgroup.mem_map_of_mem B.subtype hQnorm)

end CFSG.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentral
