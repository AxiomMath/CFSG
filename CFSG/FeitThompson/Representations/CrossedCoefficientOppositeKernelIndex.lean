module

public import CFSG.FeitThompson.Representations.RemainderControlsOtherFamilyProjections
public import CFSG.FeitThompson.Representations.DadeBetaProjectionIntegralParameter
import CFSG.FeitThompson.Representations.DadeIntegerParameterNormBounds
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CrossedKernelIndexBound

open CrossFamilyProjection (coherentImage coherentSum coherentSum_apply)
open NormalInducedWeightedNorm (weightedCoherentSum weightedCoherentSum_apply)
open MultipleRemainderProjection (coherentRemainder coherentRemainder_apply)
open DisjointCoherentFamilies (IsFullCoherentFamily isFullCoherentFamily_of_isDadeData)
open NormalInducedFamily (dadeBeta dadeBetaCoeff dadeBetaRemainder)

section Sums

variable {G : Type*} [Group G] {L : Type*} [Group L] [Fintype L]
  {ι : Type*} [Fintype ι] {ξ : ι → (L → ℂ)}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G}

theorem coherentSum_eq_weightedCoherentSum (hIrr : ∀ k, ξ k ∈ Irr L) (e : ℂ) :
    coherentSum ξ ν e = weightedCoherentSum ξ ν e := by
  rw [coherentSum_apply, weightedCoherentSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cfInner_self_of_mem_Irr (hIrr k), div_one]

end Sums

section Remainder

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} {ι : Type*} [Fintype ι] {ξ : ι → (↥L → ℂ)}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}

theorem coherentRemainder_dadeBeta_eq_dadeBetaRemainder (hIrr : ∀ k, ξ k ∈ Irr ↥L) :
    coherentRemainder (dadeBeta A R H (ξ k₀)) ξ ν k₀ (dadeBetaCoeff A R H ξ ν k₀)
        ((H.index : ℂ))
      = dadeBetaRemainder A R H ξ ν k₀ := by
  rw [coherentRemainder_apply, NormalInducedFamily.dadeBetaRemainder_apply,
    coherentSum_eq_weightedCoherentSum hIrr]
  abel

end Remainder

section Main

variable {G : Type*} [Group G] [Fintype G] {I : Type*}
  {Lsub : I → Subgroup G} [∀ i, Fintype ↥(Lsub i)] {A : I → Set G} {J : I → G → Subgroup G}
  {H : ∀ i, Subgroup ↥(Lsub i)} [∀ i, (H i).Normal]
  {ι : I → Type*} [∀ i, Finite (ι i)] {ξ : ∀ i, ι i → (↥(Lsub i) → ℂ)} {k₀ : ∀ i, ι i}
  {τ : ∀ i, charSpanZero (Set.range (ξ i)) →+ virtualChars G}
  {ν : ∀ i, Submodule.span ℤ (Set.range (ξ i)) →+ virtualChars G}

variable (hodd : Odd (Nat.card G))
  (hD : ∀ i, IsDadeData (Lsub i) (A i) (J i))
  (hA : ∀ i, A i = (fun x : ↥(Lsub i) => (x : G)) '' (((H i) : Set ↥(Lsub i)) \ {1}))
  (hS : ∀ i, Set.range (ξ i) = indFam (H i) (Irr ↥(H i) \ {1}))
  (hinj : ∀ i, Function.Injective (ξ i))
  (hIrr : ∀ i, Set.range (ξ i) ⊆ Irr ↥(Lsub i))
  (hτ : ∀ (i) (f : charSpanZero (Set.range (ξ i))) (F : dadeDomain (Lsub i) (A i)),
    (f : ↥(Lsub i) → ℂ) = (F : ↥(Lsub i) → ℂ) →
    (τ i f : G → ℂ) = ((dadeMap (hD i) F : classFun G) : G → ℂ))
  (hν : ∀ i, IsCoherentWith (Set.range (ξ i)) (τ i) (ν i))
  (hζ1 : ∀ i, ξ i (k₀ i) 1 = ((H i).index : ℂ))
  (hdisj : Pairwise fun i j =>
    Disjoint (totalDadeSupport (A i) (J i)) (totalDadeSupport (A j) (J j)))
  (hbound : ∀ i, 2 * (H i).index + 1 ≤ Nat.card ↥(H i))

omit [∀ i, Finite (ι i)] in
include hodd hD hA hS hIrr hτ hν in
theorem isFullCoherentFamily_of_config (i : I) :
    IsFullCoherentFamily (ξ i) (τ i) (ν i) (totalDadeSupport (A i) (J i)) :=
  isFullCoherentFamily_of_isDadeData hodd (hD i) (hA i) (hS i) (hIrr i)
    (fun f hf => hτ i f ⟨(f : ↥(Lsub i) → ℂ), hf⟩ rfl) (hν i)

omit [∀ i, Finite (ι i)] in
include hodd hD hA hS hIrr hτ hν in
theorem nontrivial_range_of_config (i : I) (k : ι i) : (Set.range (ξ i)).Nontrivial :=
  ⟨ξ i k, ⟨k, rfl⟩, star (ξ i k),
    (isFullCoherentFamily_of_config hodd hD hA hS hIrr hτ hν i).star_mem _ ⟨k, rfl⟩,
    fun h => (isFullCoherentFamily_of_config hodd hD hA hS hIrr hτ hν i).star_ne _ ⟨k, rfl⟩ h.symm⟩

omit [∀ i, Finite (ι i)] in
include hD hA hS hζ1 in
theorem exists_int_cfInner_dadeBeta_coherentImage (i j : I) :
    ∃ n : ℤ, cfInner (dadeBeta (A i) (J i) (H i) (ξ i (k₀ i)))
      (coherentImage (ξ j) (ν j) (k₀ j)) = (n : ℂ) := by
  have hζS : ξ i (k₀ i) ∈ indFam (H i) (Irr ↥(H i) \ {1}) := (hS i) ▸ Set.mem_range_self (k₀ i)
  exact exists_int_cfInner_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualChars
      (NormalInducedFamily.dadeBeta_mem_virtualChars (hD i) (hA i) hζS (hζ1 i)))
    (NormalInducedFamily.coherentImage_mem_span_Irr (k₀ j))

include hodd hD hA hS hinj hIrr hτ hν hζ1 hdisj hbound in
theorem div_index_le_index_sub_one_of_cfInner_ne_zero {i j : I} (hij : i ≠ j)
    (hc : cfInner (dadeBeta (A i) (J i) (H i) (ξ i (k₀ i)))
      (coherentImage (ξ j) (ν j) (k₀ j)) ≠ 0) :
    ((Nat.card ↥(H j) : ℝ) - 1) / ((H j).index : ℝ) ≤ ((H i).index : ℝ) - 1 := by
  classical
  have inst : ∀ i, Fintype (ι i) := fun i => Fintype.ofFinite _
  have hfam := isFullCoherentFamily_of_config hodd hD hA hS hIrr hτ hν
  have hS2 : ∀ i, (Set.range (ξ i)).Nontrivial := fun i =>
    nontrivial_range_of_config hodd hD hA hS hIrr hτ hν i (k₀ i)
  have hproj := MultipleRemainderProjection.sum_norm_sq_cfInner_dadeBeta_mul_le
    (a := fun i => dadeBetaCoeff (A i) (J i) (H i) (ξ i) (ν i) (k₀ i))
    hD hA hfam hdisj hinj hS hζ1 i {j} (by simp [Ne.symm hij])
  rw [Finset.sum_singleton, coherentRemainder_dadeBeta_eq_dadeBetaRemainder
    (fun k => hIrr i ⟨k, rfl⟩)] at hproj
  have hΓ := NormalInducedFamily.cfInner_self_dadeBetaRemainder_re_le_index_sub_one
    (hD i) (hA i) (hS i) (hinj i) (hν i)
    (fun f F hf => hτ i f F hf) (hIrr i ⟨k₀ i, rfl⟩) (hζ1 i) (hS2 i) (hbound i)
  obtain ⟨n, hn⟩ := exists_int_cfInner_dadeBeta_coherentImage hD hA hS hζ1 i j
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hc (by simpa using hn)
  have hone : (1 : ℝ) ≤ ‖cfInner (dadeBeta (A i) (J i) (H i) (ξ i (k₀ i)))
      (coherentImage (ξ j) (ν j) (k₀ j))‖ ^ 2 := by
    rw [hn]
    have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega)
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ |(n : ℝ)| ^ 2 := by nlinarith
      _ = ‖((n : ℤ) : ℂ)‖ ^ 2 := by
          rw [show ((n : ℤ) : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
            Real.norm_eq_abs]
  have hnn : 0 ≤ ((Nat.card ↥(H j) : ℝ) - 1) / ((H j).index : ℝ) := by
    apply div_nonneg
    · have : 1 ≤ (Nat.card ↥(H j) : ℝ) := by exact_mod_cast Nat.card_pos (α := ↥(H j))
      linarith
    · positivity
  nlinarith [hproj, hΓ, hone, hnn]

include hodd hD hA hS hinj hIrr hτ hν hζ1 hdisj hbound in
theorem card_sub_one_le_mul_of_cfInner_ne_zero {i j : I} (hij : i ≠ j)
    (hc : cfInner (dadeBeta (A i) (J i) (H i) (ξ i (k₀ i)))
      (coherentImage (ξ j) (ν j) (k₀ j)) ≠ 0) :
    (Nat.card ↥(H j) : ℤ) - 1 ≤ (((H i).index : ℤ) - 1) * ((H j).index : ℤ) := by
  have hle := div_index_le_index_sub_one_of_cfInner_ne_zero hodd hD hA hS hinj hIrr hτ hν hζ1
    hdisj hbound hij hc
  have hpos : (0 : ℝ) < ((H j).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := H j))
  rw [div_le_iff₀ hpos] at hle
  have hcast : ((Nat.card ↥(H j) : ℤ) : ℝ)
      - 1 ≤ ((((H i).index : ℤ) - 1) * ((H j).index : ℤ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast hcast

end Main

end CrossedKernelIndexBound

end CFSG.FeitThompson
