module

public import CFSG.FeitThompson.Representations.DadeBetaProjectionIntegralParameter
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open ComplexConjugate
open CrossFamilyProjection (coherentImage coherentImage_apply)
open NormalInducedWeightedNorm (weightedCoherentSum weightedCoherentSum_apply)

theorem cfInner_self_add_of_cfInner_eq_zero {X : Type*} [Fintype X] {u v : X → ℂ}
    (huv : cfInner u v = 0) (hvu : cfInner v u = 0) :
    cfInner (u + v) (u + v) = cfInner u u + cfInner v v := by
  rw [cfInner_add_left, cfInner_add_right, cfInner_add_right, huv, hvu]
  ring

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

include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem cfInner_dadeBetaRemainder_weightedCoherentSum (hS2 : (Set.range ξ).Nontrivial) :
    cfInner (dadeBetaRemainder A R H ξ ν k₀) (weightedCoherentSum ξ ν (H.index : ℂ)) = 0 := by
  rw [weightedCoherentSum_apply, cfInner_sum_right]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [cfInner_smul_right,
    cfInner_dadeBetaRemainder_coherentImage hD hA hS hinj hν hτ hζIrr hζ1 hS2 l, mul_zero]

include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem cfInner_self_dadeBetaRemainder (hS2 : (Set.range ξ).Nontrivial) :
    cfInner (dadeBetaRemainder A R H ξ ν k₀) (dadeBetaRemainder A R H ξ ν k₀)
      = (H.index : ℂ) - 1 + 2 * dadeBetaCoeff A R H ξ ν k₀
        - dadeBetaCoeff A R H ξ ν k₀ ^ 2 * (((Nat.card ↥H : ℂ) - 1) / (H.index : ℂ)) := by
  classical
  set a := dadeBetaCoeff A R H ξ ν k₀ with ha
  set Q := weightedCoherentSum ξ ν (H.index : ℂ) with hQdef
  set z := coherentImage ξ ν k₀ with hzdef
  set Γ := dadeBetaRemainder A R H ξ ν k₀ with hΓdef
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  have hac : conj a = a := by
    obtain ⟨n, hn⟩ := exists_int_dadeBetaCoeff hD hA hS hζ1
    rw [ha, hn]; simp
  have hone := cfInner_coherentImage_one hD hA hS hν hτ hζIrr hζ1 hS2
  have h1z : cfInner (1 : G → ℂ) z = 0 := by rw [← conj_cfInner, hzdef, hone k₀, map_zero]
  have hz1 : cfInner z (1 : G → ℂ) = 0 := hone k₀
  have hQ1 : cfInner Q (1 : G → ℂ) = 0 := cfInner_weightedCoherentSum_one hone
  have h1Q : cfInner (1 : G → ℂ) Q = 0 := by rw [← conj_cfInner, hQ1, map_zero]
  have hzz : cfInner z z = 1 := by
    rw [hzdef, NormalInducedWeightedNorm.cfInner_coherentImage_eq_ite H hinj hS hν k₀ k₀,
      if_pos rfl, cfInner_self_of_mem_Irr hζIrr]
  have hQz : cfInner Q z = 1 :=
    NormalInducedWeightedNorm.cfInner_weightedCoherentSum_coherentImage_of_apply_one_eq H hinj hS
      hν hζ1
  have hzQ : cfInner z Q = 1 := by rw [← conj_cfInner, hQz]; simp
  have hQQ : cfInner Q Q = ((Nat.card ↥H : ℂ) - 1) / (H.index : ℂ) :=
    NormalInducedWeightedNorm.cfInner_self_weightedCoherentSum H hinj hS hν
  have h11 : cfInner (1 : G → ℂ) (1 : G → ℂ) = 1 := cfInner_one_one
  have hΓz : cfInner Γ z = 0 :=
    cfInner_dadeBetaRemainder_coherentImage hD hA hS hinj hν hτ hζIrr hζ1 hS2 k₀
  have hΓQ : cfInner Γ Q = 0 :=
    cfInner_dadeBetaRemainder_weightedCoherentSum hD hA hS hinj hν hτ hζIrr hζ1 hS2
  have hΓ1 : cfInner Γ (1 : G → ℂ) = 0 :=
    cfInner_dadeBetaRemainder_one hD hA hS hν hτ hζIrr hζ1 hS2
  have hΓW : cfInner Γ ((1 : G → ℂ) - z + a • Q) = 0 := by
    rw [cfInner_add_right, cfInner_sub_right, cfInner_smul_right, hΓ1, hΓz, hΓQ]; ring
  have hWΓ : cfInner ((1 : G → ℂ) - z + a • Q) Γ = 0 := by
    rw [← conj_cfInner, hΓW, map_zero]
  have hWW : cfInner ((1 : G → ℂ) - z + a • Q) ((1 : G → ℂ) - z + a • Q)
      = 2 - 2 * a + a ^ 2 * (((Nat.card ↥H : ℂ) - 1) / (H.index : ℂ)) := by
    simp only [cfInner_add_left, cfInner_add_right, cfInner_sub_left, cfInner_sub_right,
      cfInner_smul_left, cfInner_smul_right, h11, h1z, hz1, hQ1, h1Q, hzz, hQz, hzQ, hQQ, hac]
    ring
  have hββ : cfInner (dadeBeta A R H (ξ k₀)) (dadeBeta A R H (ξ k₀)) = (H.index : ℂ) + 1 :=
    cfInner_self_dadeBeta hD hA hζS hζ1 hζIrr
  rw [dadeBeta_eq_add_dadeBetaRemainder,
    cfInner_self_add_of_cfInner_eq_zero hWΓ hΓW, hWW] at hββ
  linear_combination hββ

end NormalInducedFamily

end CFSG.FeitThompson
