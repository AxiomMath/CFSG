module

import CFSG.FeitThompson.Representations.ExceptionalCharInverseNorm
public import CFSG.FeitThompson.Representations.OrthogonalRemainderExactNorm
public import CFSG.FeitThompson.Definitions.DadeAveragingMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open CrossFamilyProjection (coherentImage)

theorem zero_le_int_quadratic_of_two_mul_le {e c : ℝ} (he : 0 < e) (hb : 2 * e ≤ c - 1) (n : ℤ) :
    0 ≤ (n : ℝ) ^ 2 * (c - 1) / e - 2 * (n : ℝ) := by
  have hd : 2 ≤ (c - 1) / e := by rw [le_div_iff₀ he]; linarith
  have hrw : (n : ℝ) ^ 2 * (c - 1) / e = (n : ℝ) ^ 2 * ((c - 1) / e) := by ring
  rw [hrw]
  rcases le_or_gt n 0 with hn | hn
  · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    nlinarith [sq_nonneg (n : ℝ)]
  ·
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal] {ι : Type*} [Fintype ι] {ξ : ι → (↥L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}

variable (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
  (hinj : Function.Injective ξ)
  (hν : IsCoherentWith (Set.range ξ) τ ν)
  (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζIrr : ξ k₀ ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ))
  (hS2 : (Set.range ξ).Nontrivial)
  (hbound : 2 * H.index + 1 ≤ Nat.card ↥H)

section Bounds

omit [Fintype ι] hS2 hbound in
private theorem index_pos' : 0 < (H.index : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := H))

omit [Fintype ι] hS2 in
include hbound in
private theorem two_mul_index_le' : 2 * (H.index : ℝ) ≤ (Nat.card ↥H : ℝ) - 1 := by
  have : ((2 * H.index + 1 : ℕ) : ℝ) ≤ (Nat.card ↥H : ℝ) := by exact_mod_cast hbound
  push_cast at this
  linarith

omit [Fintype ι] in
include hD hA hS hinj hν hτ hζIrr hζ1 hS2 hbound in
theorem one_sub_index_div_card_le_cfInner_self_dadeAverage_coherentImage :
    1 - (H.index : ℝ) / (Nat.card ↥H : ℝ)
      ≤ (cfInner (fun y : ↥L => dadeAverage A R (coherentImage ξ ν k₀) (y : G))
          (fun y : ↥L => dadeAverage A R (coherentImage ξ ν k₀) (y : G))).re := by
  obtain ⟨n, hn⟩ := exists_int_dadeBetaCoeff hD hA hS hζ1
  have hcard : 0 < (Nat.card ↥H : ℝ) := by exact_mod_cast Nat.card_pos (α := ↥H)
  have hF := zero_le_int_quadratic_of_two_mul_le (index_pos' (H := H)) (two_mul_index_le' hbound) n
  have key : cfInner (fun y : ↥L => dadeAverage A R (coherentImage ξ ν k₀) (y : G))
      (fun y : ↥L => dadeAverage A R (coherentImage ξ ν k₀) (y : G))
      = ((1 - (H.index : ℝ) / (Nat.card ↥H : ℝ)
        + ((n : ℝ) ^ 2 * ((Nat.card ↥H : ℝ) - 1) / (H.index : ℝ) - 2 * (n : ℝ))
          / (Nat.card ↥H : ℝ) : ℝ) : ℂ) := by
    rw [cfInner_self_dadeAverage_coherentImage hD hA hS hinj hν hτ hζIrr hζ1 hS2, hn]
    push_cast
    ring
  rw [key, Complex.ofReal_re]
  have := div_nonneg hF hcard.le
  linarith

include hD hA hS hinj hν hτ hζIrr hζ1 hS2 hbound in
theorem cfInner_self_dadeBetaRemainder_re_le_index_sub_one :
    (cfInner (dadeBetaRemainder A R H ξ ν k₀) (dadeBetaRemainder A R H ξ ν k₀)).re
      ≤ (H.index : ℝ) - 1 := by
  obtain ⟨n, hn⟩ := exists_int_dadeBetaCoeff hD hA hS hζ1
  have hF := zero_le_int_quadratic_of_two_mul_le (index_pos' (H := H)) (two_mul_index_le' hbound) n
  have key : cfInner (dadeBetaRemainder A R H ξ ν k₀) (dadeBetaRemainder A R H ξ ν k₀)
      = (((H.index : ℝ) - 1
        - ((n : ℝ) ^ 2 * ((Nat.card ↥H : ℝ) - 1) / (H.index : ℝ) - 2 * (n : ℝ)) : ℝ) : ℂ) := by
    rw [cfInner_self_dadeBetaRemainder hD hA hS hinj hν hτ hζIrr hζ1 hS2, hn]
    push_cast
    ring
  rw [key, Complex.ofReal_re]
  linarith

include hD hA hS hinj hν hτ hζIrr hζ1 hS2 hbound in
theorem cfInner_bounds_of_two_mul_index_le :
    1 - (H.index : ℝ) / (Nat.card ↥H : ℝ)
        ≤ (cfInner (fun y : ↥L => dadeAverage A R (coherentImage ξ ν k₀) (y : G))
            (fun y : ↥L => dadeAverage A R (coherentImage ξ ν k₀) (y : G))).re ∧
      (cfInner (dadeBetaRemainder A R H ξ ν k₀) (dadeBetaRemainder A R H ξ ν k₀)).re
        ≤ (H.index : ℝ) - 1 :=
  ⟨one_sub_index_div_card_le_cfInner_self_dadeAverage_coherentImage hD hA hS hinj hν hτ hζIrr hζ1
      hS2 hbound,
    cfInner_self_dadeBetaRemainder_re_le_index_sub_one hD hA hS hinj hν hτ hζIrr hζ1 hS2 hbound⟩

end Bounds

end NormalInducedFamily

end CFSG.FeitThompson
