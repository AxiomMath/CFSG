module

public import CFSG.FeitThompson.Representations.RemainderControlsOtherFamilyProjections
public import CFSG.FeitThompson.Representations.DadeBetaProjectionIntegralParameter
import CFSG.FeitThompson.Representations.DadeIntegerParameterNormBounds
import CFSG.FeitThompson.Representations.CrossedDadeScalarProductNonzero
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ZeroCrossedMass

open CrossFamilyProjection DisjointCoherentFamilies MultipleRemainderProjection
  NormalInducedFamily

noncomputable def normalMass {L : Type*} [Group L] (H : Subgroup L) : ℝ :=
  ((Nat.card H : ℝ) - 1) / ((H.index : ℝ) * (Nat.card H : ℝ))

theorem normalMass_eq {L : Type*} [Group L] (H : Subgroup L) :
    normalMass H = ((Nat.card H : ℝ) - 1) / ((H.index : ℝ) * (Nat.card H : ℝ)) := (rfl)

theorem one_le_natCard {L : Type*} [Group L] [Finite L] (H : Subgroup L) :
    (1 : ℝ) ≤ (Nat.card H : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.card_pos (α := H)).ne'

theorem normalMass_nonneg {L : Type*} [Group L] [Finite L] (H : Subgroup L) :
    0 ≤ normalMass H := by
  have h1 := one_le_natCard H
  rw [normalMass_eq]
  exact div_nonneg (by linarith) (by positivity)

theorem normalMass_eq_div_natCard {L : Type*} [Group L] [Finite L] (H : Subgroup L) :
    normalMass H = ((Nat.card H : ℝ) - 1) / (Nat.card L : ℝ) := by
  rw [normalMass_eq, ← Nat.cast_mul, Subgroup.index_mul_card]

theorem mul_normalMass_le {L : Type*} [Group L] [Finite L] (H : Subgroup L) {c : ℝ}
    (hch : c ≤ (Nat.card H : ℝ)) :
    c * normalMass H ≤ ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
  have h1 := one_le_natCard H
  have he : (0 : ℝ) ≤ (H.index : ℝ) := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < (Nat.card H : ℝ) := by linarith
  have hrw : c * normalMass H
      = (c / (Nat.card H : ℝ)) * (((Nat.card H : ℝ) - 1) / (H.index : ℝ)) := by
    rw [normalMass_eq]; ring
  rw [hrw]
  have h2 : c / (Nat.card H : ℝ) ≤ 1 := (div_le_one hpos).2 hch
  have h3 : (0 : ℝ) ≤ ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := div_nonneg (by linarith) he
  nlinarith

section Configuration

variable {G : Type*} [Group G] [Fintype G] {I : Type*}
  {Lsub : I → Subgroup G} [∀ i, Fintype ↥(Lsub i)] {A : I → Set G} {J : I → G → Subgroup G}
  {H : ∀ i, Subgroup ↥(Lsub i)} [∀ i, (H i).Normal]
  {ι : I → Type*} [∀ i, Finite (ι i)] {ξ : ∀ i, ι i → (↥(Lsub i) → ℂ)} {k₀ : ∀ i, ι i}
  {τ : ∀ i, charSpanZero (Set.range (ξ i)) →+ virtualChars G}
  {ν : ∀ i, Submodule.span ℤ (Set.range (ξ i)) →+ virtualChars G}

noncomputable def crossedProd (A : I → Set G) (J : I → G → Subgroup G)
    (H : ∀ i, Subgroup ↥(Lsub i)) (ξ : ∀ i, ι i → (↥(Lsub i) → ℂ))
    (ν : ∀ i, Submodule.span ℤ (Set.range (ξ i)) →+ virtualChars G) (k₀ : ∀ i, ι i)
    (i j : I) : ℂ :=
  cfInner (dadeBeta (A i) (J i) (H i) (ξ i (k₀ i))) (coherentImage (ξ j) (ν j) (k₀ j))

omit [∀ i, (H i).Normal] [∀ i, Finite (ι i)] in
theorem crossedProd_eq (i j : I) :
    crossedProd A J H ξ ν k₀ i j
      = cfInner (dadeBeta (A i) (J i) (H i) (ξ i (k₀ i)))
        (coherentImage (ξ j) (ν j) (k₀ j)) := (rfl)

variable (hodd : Odd (Nat.card G))
  (hDade : ∀ i, IsDadeData (Lsub i) (A i) (J i))
  (hA : ∀ i, A i = (fun x : ↥(Lsub i) => (x : G)) '' (((H i) : Set ↥(Lsub i)) \ {1}))
  (hS : ∀ i, Set.range (ξ i) = indFam (H i) (Irr ↥(H i) \ {1}))
  (hIrr : ∀ i, Set.range (ξ i) ⊆ Irr ↥(Lsub i))
  (hinj : ∀ i, Function.Injective (ξ i))
  (hν : ∀ i, IsCoherentWith (Set.range (ξ i)) (τ i) (ν i))
  (hτ : ∀ (i : I) (f : charSpanZero (Set.range (ξ i))) (F : dadeDomain (Lsub i) (A i)),
    (f : ↥(Lsub i) → ℂ) = (F : ↥(Lsub i) → ℂ) →
      (τ i f : G → ℂ) = ((dadeMap (hDade i) F : classFun G) : G → ℂ))
  (hζ1 : ∀ i, ξ i (k₀ i) 1 = ((H i).index : ℂ))
  (hdisj : Pairwise fun i j =>
    Disjoint (totalDadeSupport (A i) (J i)) (totalDadeSupport (A j) (J j)))
  (hbound : ∀ i, 2 * (H i).index + 1 ≤ Nat.card ↥(H i))

omit [∀ i, Finite (ι i)] in
include hDade hν hτ in
theorem coe_nu_eq_dadeMap (i : I) (f : Submodule.span ℤ (Set.range (ξ i)))
    (F : dadeDomain (Lsub i) (A i)) (hf : (f : ↥(Lsub i) → ℂ) = (F : ↥(Lsub i) → ℂ)) :
    (ν i f : G → ℂ) = ((dadeMap (hDade i) F : classFun G) : G → ℂ) := by
  have h1 : (1 : G) ∉ A i := fun h => ((hDade i).subset_sdiff h).2 rfl
  have hf1 : (f : ↥(Lsub i) → ℂ) 1 = 0 := by
    rw [hf]
    exact dadeDomain.apply_eq_zero F.2 (by simpa using h1)
  have hmem : (f : ↥(Lsub i) → ℂ) ∈ charSpanZero (Set.range (ξ i)) :=
    mem_charSpanZero.2 ⟨f.2, hf1⟩
  have key := (hν i).eq_on_zero ⟨(f : ↥(Lsub i) → ℂ), hmem⟩
  have harg : (Submodule.inclusion (charSpanZero_le (Set.range (ξ i)))
      ⟨(f : ↥(Lsub i) → ℂ), hmem⟩) = f := Subtype.ext rfl
  rw [harg] at key
  rw [key]
  exact hτ i _ F hf

omit [∀ i, Finite (ι i)] in
include hodd hDade hA hS hIrr hν hτ in
theorem isFullCoherentFamily_apply (i : I) :
    IsFullCoherentFamily (ξ i) (τ i) (ν i) (totalDadeSupport (A i) (J i)) :=
  isFullCoherentFamily_of_isDadeData hodd (hDade i) (hA i) (hS i) (hIrr i)
    (fun f hf => hτ i f ⟨_, hf⟩ rfl) (hν i)

omit [∀ i, Finite (ι i)] in
include hodd hDade hA hS hIrr hν hτ hζ1 hdisj in
theorem crossedProd_ne_zero {i j : I} (hij : i ≠ j) (h : crossedProd A J H ξ ν k₀ j i = 0) :
    crossedProd A J H ξ ν k₀ i j ≠ 0 := by
  have key := cfInner_dadeBeta_nu_ne_zero_or_swap (H₁ := H i) (H₂ := H j)
    (ν₁ := ν i) (ν₂ := ν j) hodd (hDade i) (hDade j) (hA i) (hA j) (hS i) (hS j)
    (hν i).inner_eq (hν j).inner_eq (coe_nu_eq_dadeMap hDade hν hτ i)
    (coe_nu_eq_dadeMap hDade hν hτ j)
    (Set.mem_range_self (k₀ i)) (hIrr i (Set.mem_range_self _)) (hζ1 i)
    (Set.mem_range_self (k₀ j)) (hIrr j (Set.mem_range_self _)) (hζ1 j) (hdisj hij)
  rw [← coherentImage_apply, ← coherentImage_apply] at key
  exact key.resolve_right (fun hc => hc h)

omit [∀ i, Finite (ι i)] in
include hDade hA hS hζ1 in
theorem one_le_norm_sq_crossedProd (i j : I) (h : crossedProd A J H ξ ν k₀ i j ≠ 0) :
    (1 : ℝ) ≤ ‖crossedProd A J H ξ ν k₀ i j‖ ^ 2 := by
  rw [crossedProd_eq] at h ⊢
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualChars (dadeBeta_mem_virtualChars (hDade i) (hA i)
      (by rw [← hS i]; exact Set.mem_range_self _) (hζ1 i)))
    (NormalInducedFamily.coherentImage_mem_span_Irr (ν := ν j) (k₀ j))
  rw [hm] at h ⊢
  have hm0 : m ≠ 0 := by intro hc; rw [hc] at h; simp at h
  have h1 : (1 : ℝ) ≤ ‖(m : ℂ)‖ := by
    rw [Complex.norm_intCast]
    have hone : (1 : ℤ) ≤ |m| := Int.one_le_abs (by omega)
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast hone
      _ = |(m : ℝ)| := by push_cast; ring
  nlinarith

section Gamma

variable [∀ i, Fintype (ι i)]

omit [Fintype G] [∀ i, Finite (ι i)] in
include hIrr in
theorem coherentSum_eq_weightedCoherentSum (i : I) (e : ℂ) :
    coherentSum (ξ i) (ν i) e = NormalInducedWeightedNorm.weightedCoherentSum (ξ i) (ν i) e := by
  rw [coherentSum_apply, NormalInducedWeightedNorm.weightedCoherentSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cfInner_self_of_mem_Irr (hIrr i ⟨k, rfl⟩), div_one]

omit [∀ i, (H i).Normal] [∀ i, Finite (ι i)] in
include hIrr in
theorem coherentRemainder_eq_dadeBetaRemainder (i : I) :
    coherentRemainder (dadeBeta (A i) (J i) (H i) (ξ i (k₀ i))) (ξ i) (ν i) (k₀ i)
        (dadeBetaCoeff (A i) (J i) (H i) (ξ i) (ν i) (k₀ i)) ((H i).index : ℂ)
      = dadeBetaRemainder (A i) (J i) (H i) (ξ i) (ν i) (k₀ i) := by
  rw [coherentRemainder_apply, dadeBetaRemainder_apply,
    coherentSum_eq_weightedCoherentSum hIrr i]
  abel

omit [∀ i, Finite (ι i)] in
include hodd hDade hA hS hIrr hinj hν hτ hζ1 hbound in
theorem cfInner_self_coherentRemainder_re_le (i : I) :
    (cfInner (coherentRemainder (dadeBeta (A i) (J i) (H i) (ξ i (k₀ i))) (ξ i) (ν i) (k₀ i)
        (dadeBetaCoeff (A i) (J i) (H i) (ξ i) (ν i) (k₀ i)) ((H i).index : ℂ))
      (coherentRemainder (dadeBeta (A i) (J i) (H i) (ξ i (k₀ i))) (ξ i) (ν i) (k₀ i)
        (dadeBetaCoeff (A i) (J i) (H i) (ξ i) (ν i) (k₀ i)) ((H i).index : ℂ))).re
      ≤ ((H i).index : ℝ) - 1 := by
  rw [coherentRemainder_eq_dadeBetaRemainder hIrr i]
  exact cfInner_self_dadeBetaRemainder_re_le_index_sub_one (hDade i) (hA i) (hS i) (hinj i)
    (hν i) (hτ i) (hIrr i (Set.mem_range_self (k₀ i))) (hζ1 i)
    (nontrivial_of_mem_of_mem_Irr (ζ := ξ i (k₀ i)) hodd (hS i) (Set.mem_range_self (k₀ i))
      (hIrr i (Set.mem_range_self (k₀ i)))) (hbound i)

end Gamma

include hodd hDade hA hS hIrr hinj hν hτ hζ1 hdisj hbound in
theorem sum_normalMass_le (i : I) (B : Finset I) (hB : ∀ j ∈ B, j ≠ i)
    (hB0 : ∀ j ∈ B, crossedProd A J H ξ ν k₀ j i = 0)
    (hstep : ∀ j ∈ B, Nat.card ↥(H i) + 2 ≤ Nat.card ↥(H j)) :
    ∑ j ∈ B, normalMass (H j) ≤ (((H i).index : ℝ) - 1) / ((Nat.card ↥(H i) : ℝ) + 2) := by
  classical
  have _ : ∀ i, Fintype (ι i) := fun i => Fintype.ofFinite (ι i)
  have hproj := sum_norm_sq_cfInner_dadeBeta_mul_le
    (a := fun i => dadeBetaCoeff (A i) (J i) (H i) (ξ i) (ν i) (k₀ i))
    hDade hA (fun i => isFullCoherentFamily_apply hodd hDade hA hS hIrr hν hτ i) hdisj hinj hS hζ1
    i B hB
  have hΓ := cfInner_self_coherentRemainder_re_le hodd hDade hA hS hIrr hinj hν hτ hζ1 hbound i
  have hsum : ∑ j ∈ B, ‖crossedProd A J H ξ ν k₀ i j‖ ^ 2
      * (((Nat.card ↥(H j) : ℝ) - 1) / ((H j).index : ℝ)) ≤ ((H i).index : ℝ) - 1 :=
    le_trans hproj hΓ
  have hterm : ∀ j ∈ B, ((Nat.card ↥(H i) : ℝ) + 2) * normalMass (H j)
      ≤ ‖crossedProd A J H ξ ν k₀ i j‖ ^ 2
        * (((Nat.card ↥(H j) : ℝ) - 1) / ((H j).index : ℝ)) := by
    intro j hj
    have hc1 := one_le_norm_sq_crossedProd hDade hA hS hζ1 i j
      (crossedProd_ne_zero hodd hDade hA hS hIrr hν hτ hζ1 hdisj (Ne.symm (hB j hj)) (hB0 j hj))
    have hcast : ((Nat.card ↥(H i) : ℝ) + 2) ≤ (Nat.card ↥(H j) : ℝ) := by
      have h := hstep j hj
      have h' : ((Nat.card ↥(H i) + 2 : ℕ) : ℝ) ≤ (Nat.card ↥(H j) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    have hmn := mul_normalMass_le (H j) (c := (Nat.card ↥(H i) : ℝ) + 2) hcast
    have hnn : (0 : ℝ) ≤ ((Nat.card ↥(H j) : ℝ) - 1) / ((H j).index : ℝ) :=
      div_nonneg (by linarith [one_le_natCard (H j)]) (Nat.cast_nonneg _)
    nlinarith
  have hkey : ((Nat.card ↥(H i) : ℝ) + 2) * ∑ j ∈ B, normalMass (H j)
      ≤ ((H i).index : ℝ) - 1 := by
    rw [Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum hterm) hsum
  rw [le_div_iff₀ (by positivity)]
  linarith

open scoped Classical in
noncomputable def zeroCrossedIndices [Fintype I] (A : I → Set G) (J : I → G → Subgroup G)
    (H : ∀ i, Subgroup ↥(Lsub i)) (ξ : ∀ i, ι i → (↥(Lsub i) → ℂ))
    (ν : ∀ i, Submodule.span ℤ (Set.range (ξ i)) →+ virtualChars G) (k₀ : ∀ i, ι i) (i : I) :
    Finset I :=
  {j ∈ Finset.univ | j ≠ i ∧ crossedProd A J H ξ ν k₀ j i = 0}

open scoped Classical in
omit [∀ i, (H i).Normal] [∀ i, Finite (ι i)] in
theorem mem_zeroCrossedIndices [Fintype I] {i j : I} :
    j ∈ zeroCrossedIndices A J H ξ ν k₀ i ↔ j ≠ i ∧ crossedProd A J H ξ ν k₀ j i = 0 := by
  simp [zeroCrossedIndices]

open scoped Classical in
include hodd hDade hA hS hIrr hinj hν hτ hζ1 hdisj hbound in
theorem sum_normalMass_zeroCrossedIndices_le [Fintype I] (i : I)
    (hstep : ∀ j ≠ i, Nat.card ↥(H i) + 2 ≤ Nat.card ↥(H j)) :
    ∑ j ∈ zeroCrossedIndices A J H ξ ν k₀ i, normalMass (H j)
      ≤ (((H i).index : ℝ) - 1) / ((Nat.card ↥(H i) : ℝ) + 2) :=
  sum_normalMass_le hodd hDade hA hS hIrr hinj hν hτ hζ1 hdisj hbound i _
    (fun _ hj => (mem_zeroCrossedIndices.1 hj).1)
    (fun _ hj => (mem_zeroCrossedIndices.1 hj).2)
    (fun _ hj => hstep _ (mem_zeroCrossedIndices.1 hj).1)

end Configuration

end ZeroCrossedMass

end CFSG.FeitThompson

end
