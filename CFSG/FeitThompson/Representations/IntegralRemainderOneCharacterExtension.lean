module

public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FeitExtension

open scoped ComplexConjugate

section Orthonormal

variable {G : Type*} [Fintype G] {ι : Type*} [Fintype ι] {η : ι → G → ℂ}

theorem cfInner_right_sum_smul (f : G → ℂ) (e : ι → ℂ) :
    cfInner f (∑ k, e k • η k) = ∑ k, conj (e k) * cfInner f (η k) := by
  simp only [cfInner_sum_right, cfInner_smul_right]

theorem cfInner_left_sum_smul (f : G → ℂ) (e : ι → ℂ) :
    cfInner (∑ k, e k • η k) f = ∑ k, e k * cfInner (η k) f := by
  simp only [cfInner_sum_left, cfInner_smul_left]

variable [DecidableEq ι]

theorem cfInner_sum_smul_left_of_orthonormal
    (hη : ∀ k l, cfInner (η k) (η l) = if k = l then (1 : ℂ) else 0) (c : ι → ℂ) (l : ι) :
    cfInner (∑ k, c k • η k) (η l) = c l := by
  rw [cfInner_left_sum_smul, Finset.sum_eq_single_of_mem l (Finset.mem_univ l)]
  · rw [hη, if_pos rfl, mul_one]
  · intro k _ hkl
    rw [hη, if_neg hkl, mul_zero]

theorem cfInner_self_add_sum_smul_of_orthonormal
    (hη : ∀ k l, cfInner (η k) (η l) = if k = l then (1 : ℂ) else 0) {Δ : G → ℂ}
    (hΔ : ∀ k, cfInner Δ (η k) = 0) (c : ι → ℂ) :
    cfInner (Δ + ∑ k, c k • η k) (Δ + ∑ k, c k • η k)
      = cfInner Δ Δ + ∑ k, c k * conj (c k) := by
  have hΔ' : ∀ k, cfInner (η k) Δ = 0 := fun k => by
    rw [← conj_cfInner, hΔ k, map_zero]
  rw [cfInner_add_left, cfInner_add_right, cfInner_add_right,
    cfInner_right_sum_smul, cfInner_left_sum_smul]
  simp only [hΔ, hΔ', mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  congr 1
  rw [cfInner_right_sum_smul]
  exact Finset.sum_congr rfl fun k _ => by
    rw [cfInner_sum_smul_left_of_orthonormal hη]; ring

end Orthonormal

theorem charSpanZero_mono {L : Type*} [Group L] {S T : Set (L → ℂ)} (h : S ⊆ T) :
    charSpanZero S ≤ charSpanZero T := fun _ hf =>
  mem_charSpanZero.2 ⟨Submodule.span_mono h (mem_charSpanZero.1 hf).1, (mem_charSpanZero.1 hf).2⟩

structure OneCharExtension (G : Type*) [Group G] [Fintype G] {L : Type*} [Group L] [Fintype L]
    {ι : Type*} [Fintype ι] (γ : ι → (L → ℂ)) (χ : L → ℂ) (d : ℤ) (k₀ : ι) where
  injective : Function.Injective γ
  mem_Irr : ∀ k, γ k ∈ Irr L
  chi_mem_Irr : χ ∈ Irr L
  chi_notMem : χ ∉ Set.range γ
  two_le_card : 2 ≤ Fintype.card ι
  tau : charSpanZero (insert χ (Set.range γ)) →+ Submodule.span ℤ (Irr G)
  nu : Submodule.span ℤ (Set.range γ) →+ Submodule.span ℤ (Irr G)
  tau_isometry : ∀ f h, cfInner (tau f : G → ℂ) (tau h : G → ℂ)
    = cfInner (f : L → ℂ) (h : L → ℂ)
  tau_apply_one : ∀ f, (tau f : G → ℂ) 1 = 0
  nu_isometry : ∀ f h, cfInner (nu f : G → ℂ) (nu h : G → ℂ)
    = cfInner (f : L → ℂ) (h : L → ℂ)
  nu_eq_tau : ∀ f : charSpanZero (Set.range γ),
    nu (Submodule.inclusion (charSpanZero_le _) f)
      = tau (Submodule.inclusion (charSpanZero_mono (Set.subset_insert χ (Set.range γ))) f)
  chi_apply_one : χ 1 = (d : ℂ) * γ k₀ 1
  d_pos : 0 < d

noncomputable def degreeSqSum {L : Type*} {ι : Type*} [One L] [Fintype ι]
    (γ : ι → (L → ℂ)) : ℂ :=
  ∑ k, γ k 1 ^ 2

theorem degreeSqSum_eq {L : Type*} {ι : Type*} [One L] [Fintype ι] (γ : ι → (L → ℂ)) :
    degreeSqSum γ = ∑ k, γ k 1 ^ 2 := (rfl)

theorem degreeSqSum_eq_sum_image {L : Type*} {ι : Type*} [One L] [Fintype ι]
    [DecidableEq (L → ℂ)] {γ : ι → (L → ℂ)} (h : Function.Injective γ) :
    degreeSqSum γ = ∑ f ∈ Finset.univ.image γ, f 1 ^ 2 := by
  rw [degreeSqSum_eq, Finset.sum_image fun _ _ _ _ he => h he]

namespace OneCharExtension

variable {G : Type*} [Group G] [Fintype G] {L : Type*} [Group L] [Fintype L]
  {ι : Type*} [Fintype ι] {γ : ι → (L → ℂ)} {χ : L → ℂ} {d : ℤ} {k₀ : ι}
  (E : OneCharExtension G γ χ d k₀)

noncomputable def nuImage (k : ι) : G → ℂ :=
  (E.nu ⟨γ k, Submodule.subset_span ⟨k, rfl⟩⟩ : G → ℂ)

theorem nuImage_apply (k : ι) :
    E.nuImage k = (E.nu ⟨γ k, Submodule.subset_span ⟨k, rfl⟩⟩ : G → ℂ) := (rfl)

theorem nuImage_mem_span_Irr (k : ι) : E.nuImage k ∈ Submodule.span ℤ (Irr G) :=
  (E.nu ⟨γ k, Submodule.subset_span ⟨k, rfl⟩⟩).2

theorem nuImage_mem_virtualChars (k : ι) : E.nuImage k ∈ virtualChars G :=
  span_Irr_le_virtualChars (E.nuImage_mem_span_Irr k)

theorem cfInner_nuImage_self (k : ι) : cfInner (E.nuImage k) (E.nuImage k) = 1 := by
  rw [nuImage, E.nu_isometry]
  exact cfInner_self_of_mem_Irr (E.mem_Irr k)

theorem cfInner_nuImage_of_ne {k l : ι} (h : k ≠ l) :
    cfInner (E.nuImage k) (E.nuImage l) = 0 := by
  rw [nuImage, nuImage, E.nu_isometry]
  exact cfInner_eq_zero_of_mem_Irr (E.mem_Irr k) (E.mem_Irr l) fun he => h (E.injective he)

theorem cfInner_nuImage_nuImage [DecidableEq ι] (k l : ι) :
    cfInner (E.nuImage k) (E.nuImage l) = if k = l then 1 else 0 := by
  by_cases h : k = l
  · subst h; rw [if_pos rfl, E.cfInner_nuImage_self]
  · rw [if_neg h, E.cfInner_nuImage_of_ne h]

include E in
theorem sub_smul_mem_charSpanZero :
    χ - (d : ℂ) • γ k₀ ∈ charSpanZero (insert χ (Set.range γ)) := by
  refine mem_charSpanZero.2
    ⟨Submodule.sub_mem _ (Submodule.subset_span (Set.mem_insert _ _)) ?_, ?_⟩
  · rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨k₀, rfl⟩))
  · simp [E.chi_apply_one]

noncomputable def alpha : G → ℂ :=
  (E.tau ⟨χ - (d : ℂ) • γ k₀, E.sub_smul_mem_charSpanZero⟩ : G → ℂ)

theorem alpha_apply :
    E.alpha = (E.tau ⟨χ - (d : ℂ) • γ k₀, E.sub_smul_mem_charSpanZero⟩ : G → ℂ) := (rfl)

theorem alpha_mem_span_Irr : E.alpha ∈ Submodule.span ℤ (Irr G) :=
  (E.tau ⟨χ - (d : ℂ) • γ k₀, E.sub_smul_mem_charSpanZero⟩).2

theorem alpha_mem_virtualChars : E.alpha ∈ virtualChars G :=
  span_Irr_le_virtualChars E.alpha_mem_span_Irr

theorem alpha_apply_one : E.alpha 1 = 0 := E.tau_apply_one _

theorem cfInner_self_alpha : cfInner E.alpha E.alpha = 1 + (d : ℂ) ^ 2 := by
  have hne : χ ≠ γ k₀ := fun h => E.chi_notMem ⟨k₀, h.symm⟩
  rw [alpha, E.tau_isometry]
  change cfInner (χ - (d : ℂ) • γ k₀) (χ - (d : ℂ) • γ k₀) = _
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left,
    cfInner_smul_right, cfInner_smul_right, cfInner_smul_left,
    cfInner_self_of_mem_Irr E.chi_mem_Irr, cfInner_self_of_mem_Irr (E.mem_Irr k₀),
    cfInner_eq_zero_of_mem_Irr E.chi_mem_Irr (E.mem_Irr k₀) hne,
    cfInner_eq_zero_of_mem_Irr (E.mem_Irr k₀) E.chi_mem_Irr (Ne.symm hne)]
  simp only [map_intCast, mul_zero, mul_one, sub_zero, zero_sub, sub_neg_eq_add]
  ring

variable [DecidableEq ι]

noncomputable def bCoeff (k : ι) : ℂ :=
  cfInner E.alpha (E.nuImage k) + (d : ℂ) * (if k = k₀ then 1 else 0)

theorem bCoeff_apply (k : ι) :
    E.bCoeff k = cfInner E.alpha (E.nuImage k) + (d : ℂ) * (if k = k₀ then 1 else 0) := (rfl)

theorem bCoeff_of_ne {k : ι} (h : k ≠ k₀) : E.bCoeff k = cfInner E.alpha (E.nuImage k) := by
  rw [bCoeff, if_neg h]; ring

theorem bCoeff_self : E.bCoeff k₀ = cfInner E.alpha (E.nuImage k₀) + (d : ℂ) := by
  rw [bCoeff, if_pos rfl, mul_one]

noncomputable def remainder : G → ℂ :=
  E.alpha + (d : ℂ) • E.nuImage k₀ - ∑ k, E.bCoeff k • E.nuImage k

theorem remainder_apply :
    E.remainder = E.alpha + (d : ℂ) • E.nuImage k₀ - ∑ k, E.bCoeff k • E.nuImage k := (rfl)

theorem exists_int_bCoeff (k : ι) : ∃ m : ℤ, E.bCoeff k = (m : ℂ) := by
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr E.alpha_mem_span_Irr
    (E.nuImage_mem_span_Irr k)
  refine ⟨m + d * (if k = k₀ then 1 else 0), ?_⟩
  rw [bCoeff, hm]
  split <;> push_cast <;> ring

theorem conj_bCoeff (k : ι) : conj (E.bCoeff k) = E.bCoeff k := by
  obtain ⟨m, hm⟩ := E.exists_int_bCoeff k
  rw [hm, map_intCast]

theorem remainder_mem_span_Irr : E.remainder ∈ Submodule.span ℤ (Irr G) := by
  have key : ∀ (m : ℤ) (f : G → ℂ), f ∈ Submodule.span ℤ (Irr G) →
      (m : ℂ) • f ∈ Submodule.span ℤ (Irr G) := by
    intro m f hf
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ hf
  refine Submodule.sub_mem _
    (Submodule.add_mem _ E.alpha_mem_span_Irr (key d _ (E.nuImage_mem_span_Irr k₀)))
    (Submodule.sum_mem _ fun k _ => ?_)
  obtain ⟨m, hm⟩ := E.exists_int_bCoeff k
  rw [hm]
  exact key m _ (E.nuImage_mem_span_Irr k)

theorem remainder_mem_virtualChars : E.remainder ∈ virtualChars G :=
  span_Irr_le_virtualChars E.remainder_mem_span_Irr

theorem cfInner_remainder_nuImage (k : ι) : cfInner E.remainder (E.nuImage k) = 0 := by
  rw [remainder, cfInner_sub_left, cfInner_add_left, cfInner_smul_left,
    cfInner_sum_smul_left_of_orthonormal E.cfInner_nuImage_nuImage,
    E.cfInner_nuImage_nuImage, bCoeff]
  by_cases hk : k = k₀
  · subst hk; simp
  · rw [if_neg (Ne.symm hk), if_neg hk]; ring

theorem alpha_eq :
    E.alpha = E.remainder
      + ∑ k, (E.bCoeff k - (d : ℂ) * (if k = k₀ then 1 else 0)) • E.nuImage k := by
  have hsplit : ∑ k, (E.bCoeff k - (d : ℂ) * (if k = k₀ then 1 else 0)) • E.nuImage k
      = (∑ k, E.bCoeff k • E.nuImage k) - (d : ℂ) • E.nuImage k₀ := by
    rw [Finset.sum_congr rfl (fun k _ =>
      sub_smul (E.bCoeff k) ((d : ℂ) * (if k = k₀ then 1 else 0)) (E.nuImage k)),
      Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_univ k₀)]
    · rw [if_pos rfl, mul_one]
    · intro k _ hk; rw [if_neg hk, mul_zero, zero_smul]
  rw [hsplit, remainder]
  abel

theorem cfInner_self_remainder_add_sum_sq :
    cfInner E.remainder E.remainder + ∑ k, E.bCoeff k ^ 2
      = 1 + 2 * (d : ℂ) * E.bCoeff k₀ := by
  have hpy := cfInner_self_add_sum_smul_of_orthonormal E.cfInner_nuImage_nuImage
    E.cfInner_remainder_nuImage
    (fun k => E.bCoeff k - (d : ℂ) * (if k = k₀ then 1 else 0))
  rw [← E.alpha_eq, E.cfInner_self_alpha] at hpy
  have hcc : ∀ k : ι, (E.bCoeff k - (d : ℂ) * (if k = k₀ then 1 else 0))
      * conj (E.bCoeff k - (d : ℂ) * (if k = k₀ then 1 else 0))
      = E.bCoeff k ^ 2 + (if k = k₀ then (d : ℂ) ^ 2 - 2 * (d : ℂ) * E.bCoeff k₀ else 0) := by
    intro k
    have hconj : conj (E.bCoeff k - (d : ℂ) * (if k = k₀ then 1 else 0))
        = E.bCoeff k - (d : ℂ) * (if k = k₀ then 1 else 0) := by
      simp only [map_sub, map_mul, map_intCast, E.conj_bCoeff]
      congr 1
      split <;> simp
    rw [hconj]
    by_cases hk : k = k₀
    · subst hk; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg hk, if_neg hk]; ring
  rw [Finset.sum_congr rfl fun k _ => hcc k, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ k₀ _, if_pos (Finset.mem_univ k₀)] at hpy
  linear_combination -hpy

theorem int_remainder_add_sum_sq {b : ι → ℤ} (hb : ∀ k, E.bCoeff k = (b k : ℂ)) {n : ℤ}
    (hn : cfInner E.remainder E.remainder = (n : ℂ)) :
    n + ∑ k, b k ^ 2 = 1 + 2 * d * b k₀ := by
  have h := E.cfInner_self_remainder_add_sum_sq
  rw [hn, Finset.sum_congr rfl fun k _ => by rw [hb k], hb k₀] at h
  exact_mod_cast h

theorem exists_int_cfInner_self_remainder :
    ∃ n : ℤ, cfInner E.remainder E.remainder = (n : ℂ) :=
  exists_int_cfInner_of_mem_span_Irr E.remainder_mem_span_Irr E.remainder_mem_span_Irr

end OneCharExtension

end FeitExtension

end CFSG.FeitThompson
