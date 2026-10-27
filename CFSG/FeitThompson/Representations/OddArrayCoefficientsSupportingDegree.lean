module

public import CFSG.FeitThompson.Representations.DadeIntegerParameterNormBounds
public import CFSG.FeitThompson.Representations.CoherentConjugateDifferenceBetaProduct
public import CFSG.FeitThompson.Representations.SaturatedSignedArraySingleCharacter
public import CFSG.FeitThompson.Representations.ArrayProjectionEnergySaturation
public import CFSG.FeitThompson.Representations.OddAdditiveArrayCoefficients
public import CFSG.FeitThompson.Representations.IntegerNormBoundEqualitySignedBlocks
public import CFSG.FeitThompson.Representations.WitnessCongruenceLocalInverseNormBound
public import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray
public import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open CrossFamilyProjection (coherentImage coherentImage_apply)
open NormalInducedWeightedNorm (weightedCoherentSum weightedCoherentSum_apply)

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} {ι : Type*} [Fintype ι] {ξ : ι → (↥L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}
  {m n : ℕ} [NeZero m] [NeZero n] {θ : Fin m × Fin n → G → ℂ} {b : Fin m × Fin n → ℤ}

noncomputable def dadeBetaCoherentPart (A : Set G) (R : G → Subgroup G) (H : Subgroup ↥L)
    (ξ : ι → (↥L → ℂ)) (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (k₀ : ι) : G → ℂ :=
  -coherentImage ξ ν k₀ + dadeBetaCoeff A R H ξ ν k₀ • weightedCoherentSum ξ ν (H.index : ℂ)

theorem dadeBetaCoherentPart_apply :
    dadeBetaCoherentPart A R H ξ ν k₀ = -coherentImage ξ ν k₀
      + dadeBetaCoeff A R H ξ ν k₀ • weightedCoherentSum ξ ν (H.index : ℂ) := (rfl)

omit [Fintype G] [Fintype ↥L] [Fintype ι] in
theorem coherentImage_mem_classFun (l : ι) : coherentImage ξ ν l ∈ classFun G :=
  virtualChars_le_classFun (mem_virtualChars_of_mem_span_Irr (coherentImage_mem_span_Irr l))

omit [Fintype G] in
theorem weightedCoherentSum_mem_classFun (e : ℂ) : weightedCoherentSum ξ ν e ∈ classFun G := by
  refine Submodule.span_le.2 ?_ (NormalInducedWeightedNorm.weightedCoherentSum_mem_span e)
  rintro f ⟨l, rfl⟩
  exact coherentImage_mem_classFun l

theorem dadeBetaCoherentPart_mem_classFun :
    dadeBetaCoherentPart A R H ξ ν k₀ ∈ classFun G := by
  rw [dadeBetaCoherentPart_apply]
  exact add_mem (neg_mem (coherentImage_mem_classFun k₀))
    (Submodule.smul_mem _ _ (weightedCoherentSum_mem_classFun _))

theorem dadeBeta_eq_one_add_dadeBetaCoherentPart_add_dadeBetaRemainder :
    dadeBeta A R H (ξ k₀) = 1 + dadeBetaCoherentPart A R H ξ ν k₀
      + dadeBetaRemainder A R H ξ ν k₀ := by
  rw [dadeBeta_eq_add_dadeBetaRemainder (ν := ν), dadeBetaCoherentPart_apply]
  abel

theorem cfInner_weightedCoherentSum_of_forall {ψ : G → ℂ} (e : ℂ)
    (h : ∀ l : ι, cfInner (coherentImage ξ ν l) ψ = 0) :
    cfInner (weightedCoherentSum ξ ν e) ψ = 0 := by
  rw [weightedCoherentSum_apply, cfInner_sum_left]
  exact Finset.sum_eq_zero fun l _ => by rw [cfInner_smul_left, h l, mul_zero]

theorem cfInner_dadeBetaCoherentPart_of_forall {ψ : G → ℂ}
    (h : ∀ l : ι, cfInner (coherentImage ξ ν l) ψ = 0) :
    cfInner (dadeBetaCoherentPart A R H ξ ν k₀) ψ = 0 := by
  rw [dadeBetaCoherentPart_apply, cfInner_add_left, cfInner_neg_left, cfInner_smul_left,
    h k₀, cfInner_weightedCoherentSum_of_forall _ h]
  ring

theorem dadeBetaRemainder_mem_classFun [H.Normal] (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hS : Set.range ξ = indFam H (Irr ↥H \ {1})) (hζ1 : ξ k₀ 1 = (H.index : ℂ)) :
    dadeBetaRemainder A R H ξ ν k₀ ∈ classFun G := by
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  rw [dadeBetaRemainder_apply]
  exact sub_mem (dadeBeta_mem_classFun hD hA hζS hζ1)
    (add_mem (sub_mem (one_mem_classFun G) (coherentImage_mem_classFun k₀))
      (Submodule.smul_mem _ _ (weightedCoherentSum_mem_classFun _)))

omit [Fintype G] [Fintype ↥L] [Fintype ι] in
theorem mem_cauchySchwarzClassFun_of_mem_classFun {f : G → ℂ} (hf : f ∈ classFun G) :
    f ∈ CauchySchwarzProjection.classFun G :=
  CauchySchwarzProjection.mem_classFun.2 fun g x => classFun.apply_conj hf g x

omit [Group G] [Fintype ↥L] [Fintype ι] in
theorem cfInner_self_eq_ofReal_re (f : G → ℂ) :
    cfInner f f = (((cfInner f f).re : ℝ) : ℂ) := by
  rw [cfInner_self_re]; exact cfInner_self_eq_ofReal f

omit [Group G] [Fintype ↥L] [Fintype ι] [NeZero m] [NeZero n] in
theorem cfInner_sum_smul_right_eq_zero {ψ : G → ℂ} (c : Fin m × Fin n → ℂ)
    (h : ∀ p, cfInner ψ (θ p) = 0) : cfInner ψ (∑ p, c p • θ p) = 0 := by
  rw [cfInner_sum_smul_right]
  exact Finset.sum_eq_zero fun p _ => by rw [h p, mul_zero]

section Main

variable [H.Normal] (hodd : Odd (Nat.card G)) (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
  (hinj : Function.Injective ξ)
  (hν : IsCoherentWith (Set.range ξ) τ ν)
  (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζIrr : ξ k₀ ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ))
  (hS2 : (Set.range ξ).Nontrivial)
  (hbound : 2 * H.index + 1 ≤ Nat.card ↥H)
  (hθ : IsOrthonormalFamily θ) (hθmem : ∀ p, θ p ∈ virtualChars G) (hθ0 : θ (0, 0) = 1)
  (hθν : ∀ (l : ι) (p : Fin m × Fin n), cfInner (coherentImage ξ ν l) (θ p) = 0)
  (hb : ∀ p, cfInner (dadeBeta A R H (ξ k₀)) (θ p) = (b p : ℂ))

omit [Fintype ι] in
include hD hν hτ in
theorem coe_nu_eq_dadeMap (f : Submodule.span ℤ (Set.range ξ)) (F : dadeDomain L A)
    (h : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
  rw [← coherentHomSpan_coe (ν := ν)]
  exact coherentHomSpan_eq_dadeMap hD hν hτ f F h

omit [Fintype ι] [NeZero m] [NeZero n] [H.Normal] in
include hS hθν in
theorem cfInner_nu_star_eq_zero (p : Fin m × Fin n) :
    cfInner (ν ⟨star (ξ k₀), Submodule.subset_span
        (star_mem_of_mem hS (Set.mem_range_self k₀))⟩ : G → ℂ) (θ p) = 0 := by
  obtain ⟨l, hl⟩ := star_mem_of_mem hS (Set.mem_range_self k₀)
  have heq : (⟨star (ξ k₀), Submodule.subset_span
      (star_mem_of_mem hS (Set.mem_range_self k₀))⟩ : Submodule.span ℤ (Set.range ξ))
      = ⟨ξ l, Submodule.subset_span ⟨l, rfl⟩⟩ := Subtype.ext hl.symm
  rw [heq, ← coherentImage_apply]
  exact hθν l p

omit [Fintype ι] [NeZero m] [NeZero n] in
include hD hA hS hζ1 hθmem in
theorem exists_int_cfInner_dadeBeta_array :
    ∃ c : Fin m × Fin n → ℤ, ∀ p, cfInner (dadeBeta A R H (ξ k₀)) (θ p) = (c p : ℂ) := by
  choose c hc using fun p => exists_int_cfInner_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualChars
      (dadeBeta_mem_virtualChars hD hA (hS ▸ Set.mem_range_self k₀) hζ1))
    (mem_span_Irr_of_mem_virtualChars (hθmem p))
  exact ⟨c, hc⟩

omit [Fintype ι] in
include hD hA hS hζ1 hθ0 hb in
theorem array_coeff_zero_eq_one : b (0, 0) = 1 := by
  have h := hb (0, 0)
  rw [hθ0, cfInner_dadeBeta_one hD hA (hS ▸ Set.mem_range_self k₀) hζ1] at h
  exact_mod_cast h.symm

include hD hA hS hinj hν hτ hζIrr hζ1 hS2 hbound hθ hθmem hθ0 hθν hb in
theorem dade_array_saturation
    (hexch : ∀ (i : Fin m) (j : Fin n), b (i, j) + b (0, 0) = b (i, 0) + b (0, j))
    (hrow : ∀ i : Fin m, Odd (b (i, 0))) (hcol : ∀ j : Fin n, Odd (b (0, j)))
    (hemn : (H.index : ℤ) ≤ (m : ℤ) * n) :
    (H.index : ℤ) = (m : ℤ) * n ∧ (∀ p, b p = 1 ∨ b p = -1) ∧
      dadeBetaRemainder A R H ξ ν k₀ + 1 = ∑ p, ((b p : ℤ) : ℂ) • θ p := by
  have h00 : b (0, 0) = 1 := array_coeff_zero_eq_one hD hA hS hζ1 hθ0 hb
  have hoddb : ∀ p : Fin m × Fin n, Odd (b p) := fun p => by
    simpa using odd_of_axes_odd (a := fun i j => b (i, j)) h00 hexch hrow hcol p.1 p.2
  refine CauchySchwarzProjection.array_energy_saturation (e := (H.index : ℤ))
    hθmem (fun p q => by
      rw [CauchySchwarzProjection.classFunInner_eq_cfInner]; exact hθ.cfInner_eq_ite p q)
    hθ0
    (dadeBeta_mem_virtualChars hD hA (hS ▸ Set.mem_range_self k₀) hζ1)
    (mem_cauchySchwarzClassFun_of_mem_classFun dadeBetaCoherentPart_mem_classFun)
    (mem_cauchySchwarzClassFun_of_mem_classFun (dadeBetaRemainder_mem_classFun hD hA hS hζ1))
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Subgroup.index_ne_zero_of_finite (H := H)))
    hemn
    dadeBeta_eq_one_add_dadeBetaCoherentPart_add_dadeBetaRemainder
    (fun p => by
      rw [CauchySchwarzProjection.classFunInner_eq_cfInner]
      exact cfInner_dadeBetaCoherentPart_of_forall (fun l => hθν l p))
    (by
      rw [CauchySchwarzProjection.classFunInner_eq_cfInner]
      exact cfInner_dadeBetaRemainder_one hD hA hS hν hτ hζIrr hζ1 hS2)
    ?_
    (fun p => by rw [CauchySchwarzProjection.classFunInner_eq_cfInner]; exact hb p)
    hoddb
  ·
    rw [CauchySchwarzProjection.classFunInner_eq_cfInner,
      cfInner_self_eq_ofReal_re (dadeBetaRemainder A R H ξ ν k₀),
      show (((H.index : ℤ) : ℂ) - 1) = (((H.index : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.real_le_real]
    exact cfInner_self_dadeBetaRemainder_re_le_index_sub_one hD hA hS hinj hν hτ hζIrr hζ1
      hS2 hbound

include hodd hD hA hS hinj hν hτ hζIrr hζ1 hS2 hbound hθ hθmem hθ0 hθν hb in
theorem dade_signed_array_decomposition
    (hexch : ∀ (i : Fin m) (j : Fin n), b (i, j) + b (0, 0) = b (i, 0) + b (0, j))
    (hrow : ∀ i : Fin m, Odd (b (i, 0))) (hcol : ∀ j : Fin n, Odd (b (0, j)))
    (hemn : (H.index : ℤ) ≤ (m : ℤ) * n) :
    (H.index : ℤ) = (m : ℤ) * n ∧
      ∃ ε : Fin m × Fin n → ℂ, (∀ p, ε p = 1 ∨ ε p = -1) ∧
        (∑ p, ε p • θ p) = dadeBetaRemainder A R H ξ ν k₀ + 1 ∧
        ∃ χ : G → ℂ, χ ∈ signedIrr G ∧
          (χ = (ν ⟨ξ k₀, Submodule.subset_span (Set.mem_range_self k₀)⟩ : G → ℂ) ∨
            χ = -(ν ⟨star (ξ k₀), Submodule.subset_span
              (star_mem_of_mem hS (Set.mem_range_self k₀))⟩ : G → ℂ)) ∧
          dadeBeta A R H (ξ k₀) = (∑ p, ε p • θ p) - χ ∧ ∀ p, IsOrthogonal χ (θ p) := by
  classical
  obtain ⟨hemn', hsign, hX⟩ := dade_array_saturation hD hA hS hinj hν hτ hζIrr hζ1 hS2 hbound
    hθ hθmem hθ0 hθν hb hexch hrow hcol hemn
  have hεsign : ∀ p, ((b p : ℤ) : ℂ) = 1 ∨ ((b p : ℤ) : ℂ) = -1 := fun p => by
    rcases hsign p with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  have hβX : dadeBeta A R H (ξ k₀) - ∑ p, ((b p : ℤ) : ℂ) • θ p
      = dadeBetaCoherentPart A R H ξ ν k₀ := by
    rw [← hX, dadeBeta_eq_one_add_dadeBetaCoherentPart_add_dadeBetaRemainder (ν := ν)]
    abel
  have hperp : ∀ p, IsOrthogonal (dadeBeta A R H (ξ k₀) - ∑ p, ((b p : ℤ) : ℂ) • θ p) (θ p) :=
    fun p => by
      rw [isOrthogonal_iff, hβX]
      exact cfInner_dadeBetaCoherentPart_of_forall (fun l => hθν l p)
  have hnorm : cfInner (dadeBeta A R H (ξ k₀)) (dadeBeta A R H (ξ k₀)) = (m : ℂ) * n + 1 := by
    rw [cfInner_self_dadeBeta hD hA (hS ▸ Set.mem_range_self k₀) hζ1 hζIrr]
    have h : ((H.index : ℂ)) = (m : ℂ) * n := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hemn'
    rw [h]
  obtain ⟨hχsigned, hχperp, hβeq⟩ := isSignedIrr_sub_of_saturated_signed_array_fin
    (η := θ) (ε := fun p => ((b p : ℤ) : ℂ)) (β := dadeBeta A R H (ξ k₀))
    (χ := (∑ p, ((b p : ℤ) : ℂ) • θ p) - dadeBeta A R H (ξ k₀))
    hθ (fun p => mem_span_Irr_of_mem_virtualChars (hθmem p)) hεsign
    (mem_span_Irr_of_mem_virtualChars
      (dadeBeta_mem_virtualChars hD hA (hS ▸ Set.mem_range_self k₀) hζ1))
    hnorm hperp rfl
  refine ⟨hemn', fun p => ((b p : ℤ) : ℂ), hεsign, hX.symm,
    (∑ p, ((b p : ℤ) : ℂ) • θ p) - dadeBeta A R H (ξ k₀), hχsigned, ?_, hβeq, hχperp⟩
  have hρθ : ∀ p, cfInner ((ν ⟨ξ k₀, Submodule.subset_span (Set.mem_range_self k₀)⟩ : G → ℂ)
      - (ν ⟨star (ξ k₀), Submodule.subset_span
        (star_mem_of_mem hS (Set.mem_range_self k₀))⟩ : G → ℂ)) (θ p) = 0 := fun p => by
    rw [cfInner_sub_left, cfInner_nu_star_eq_zero hS hθν p, ← coherentImage_apply, hθν k₀ p]
    ring
  have hone : cfInner ((ν ⟨ξ k₀, Submodule.subset_span (Set.mem_range_self k₀)⟩ : G → ℂ)
      - (ν ⟨star (ξ k₀), Submodule.subset_span
        (star_mem_of_mem hS (Set.mem_range_self k₀))⟩ : G → ℂ))
      ((∑ p, ((b p : ℤ) : ℂ) • θ p) - dadeBeta A R H (ξ k₀)) = 1 := by
    rw [cfInner_sub_right, cfInner_sum_smul_right_eq_zero _ hρθ,
      cfInner_nu_sub_nu_star_dadeBeta hodd hD hA hS (coe_nu_eq_dadeMap hD hν hτ)
        (Set.mem_range_self k₀) hζIrr hζ1]
    ring
  exact eq_or_eq_neg_of_cfInner_sub_eq_one
    (nu_mem_signedIrr hodd hD hA hS hν.inner_eq (coe_nu_eq_dadeMap hD hν hτ)
      (Set.mem_range_self k₀) hζIrr)
    (nu_star_mem_signedIrr hodd hD hA hS hν.inner_eq (coe_nu_eq_dadeMap hD hν hτ)
      (Set.mem_range_self k₀) hζIrr)
    hχsigned
    (isOrthogonal_iff.1
      (isOrthogonal_nu_nu_star hodd hS hν.inner_eq (Set.mem_range_self k₀) hζIrr)) hone

end Main

end NormalInducedFamily

end CFSG.FeitThompson

end
