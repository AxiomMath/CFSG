module

public import CFSG.FeitThompson.Representations.CoherenceDeterminesUniformBridgeImage
import CFSG.FeitThompson.Representations.CoherentSubfamilyCyclicArrayOrthogonal
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.InducedFamilyIrreducibleRowOrthogonal
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace LargeLinearLayer

open Finset

theorem eq_zero_of_mul_sq_le {c a : ℤ} (hc : 8 ≤ c) (hle : c * a ^ 2 ≤ 4 * a + 2) : a = 0 := by
  rcases lt_trichotomy a 0 with hneg | h0 | hpos
  · exfalso
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ c - 8) (sq_nonneg a),
      mul_nonneg (by omega : (0 : ℤ) ≤ -(a + 1)) (by omega : (0 : ℤ) ≤ -a)]
  · exact h0
  · exfalso
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ c - 8) (sq_nonneg a),
      mul_nonneg (by omega : (0 : ℤ) ≤ a - 1) (by omega : (0 : ℤ) ≤ a)]

theorem sum_sq_sub_two_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι) (a : ℤ) :
    ∑ x : ι, (a - 2 * (if x = z then 1 else 0)) ^ 2
      = (Fintype.card ι : ℤ) * a ^ 2 + 4 - 4 * a := by
  have h1 : ∀ x : ι, (a - 2 * (if x = z then 1 else 0)) ^ 2
      = a ^ 2 + (4 - 4 * a) * (if x = z then 1 else 0) := by
    intro x
    by_cases hx : x = z
    · simp [hx]; ring
    · simp [hx]
  rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib, Finset.sum_const,
    ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ z (fun _ => (1 : ℤ))]
  simp only [if_pos (Finset.mem_univ z), mul_one, Finset.card_univ, nsmul_eq_mul]
  ring

theorem eq_zero_of_sum_sq_le_six {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι)
    (hcard : 8 ≤ Fintype.card ι) {a : ℤ}
    (hle : ∑ x : ι, (a - 2 * (if x = z then 1 else 0)) ^ 2 ≤ 6) : a = 0 := by
  rw [sum_sq_sub_two_ite z a] at hle
  have hc : (8 : ℤ) ≤ (Fintype.card ι : ℤ) := by exact_mod_cast hcard
  exact eq_zero_of_mul_sq_le hc (by omega)

structure IsLargeLinearLayerData {G : Type*} [Group G] [Fintype G] {L : Subgroup G}
    [Fintype ↥L] {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L)
    (ζ : ↥L → ℂ) (d δ : ℤ) (A : Set G) (T : G → Subgroup G)
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G)
    (P : Set (↥L → ℂ)) (τ : charSpanZero P →+ virtualChars G)
    (ν : Submodule.span ℤ P →+ virtualChars G) : Prop where
  local_data : h.IsUniformBridgeData σ ζ d 2 δ
  odd : Odd (Nat.card G)
  isDadeData : IsDadeData L A T
  image_subset : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A
  isCyclicTIPair :
    IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
  omega_isometry : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
    (W₂.map L.subtype) ω
  subset_indFam : P ⊆ indFam K (Irr ↥K \ {1})
  subset_Irr : P ⊆ Irr ↥L
  star_mem : ∀ χ ∈ P, star χ ∈ P
  eight_le : 8 ≤ P.ncard
  zeta_mem : ζ ∈ P
  degree_eq : ∀ χ ∈ P, χ 1 = (Nat.card ↥W₁ : ℂ)
  coherent : IsCoherentWith P τ ν
  tau_eq : ∀ (f : charSpanZero P) (F : dadeDomain L A), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
    (τ f : G → ℂ) = ((dadeMap isDadeData F : classFun G) : G → ℂ)

namespace IsLargeLinearLayerData

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ζ : ↥L → ℂ} {d δ : ℤ} {A : Set G} {T : G → Subgroup G}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {P : Set (↥L → ℂ)} {τ : charSpanZero P →+ virtualChars G}
  {ν : Submodule.span ℤ P →+ virtualChars G}
  (hC : IsLargeLinearLayerData h σ ζ d δ A T ω P τ ν)

omit [K.Normal] in
include hC in
theorem finite_family : P.Finite := Set.Finite.subset finite_Irr hC.subset_Irr

omit [K.Normal] in
include hC in
theorem image_sdiff_subset : (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) ⊆ A := by
  rintro g ⟨x, ⟨hxK, hx1⟩, rfl⟩
  exact hC.image_subset
    ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hxK (by simpa using hx1), rfl⟩

omit [K.Normal] in
include hC in
theorem cyclicTIDiff_subset_param :
    cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ⊆ A := by
  intro g hg
  rw [← image_cyclicTIset_eq] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact hC.image_subset ⟨x, mem_primeTIbridgeSupport_of_isConj hx (IsConj.refl _), rfl⟩

omit [K.Normal] in
include hC in
theorem span_le_virtualChars : Submodule.span ℤ P ≤ virtualChars ↥L :=
  Submodule.span_le.2 fun _ hx => Irr_subset_virtualChars (hC.subset_Irr hx)

include hC in
theorem mem_dadeZDomain_of_mem_charSpanZero {f : ↥L → ℂ} (hf : f ∈ charSpanZero P) :
    f ∈ dadeZDomain L A :=
  mem_dadeZDomain.2 ⟨hC.span_le_virtualChars (charSpanZero_le _ hf), fun y hy =>
    PartialCoherent.apply_eq_zero_of_notMem hC.image_sdiff_subset hC.subset_indFam ⟨f, hf⟩ y hy⟩

noncomputable def tauBridge (hC : IsLargeLinearLayerData h σ ζ d δ A T ω P τ ν)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) : G → ℂ :=
  ((dadeZMap hC.isDadeData
      ⟨h.primeTIbridge σ ζ δ 2 i j,
        primeTIbridge_mem_dadeZDomain hC.local_data hC.image_subset i hj⟩ :
    charSpanZero (Irr G)) : G → ℂ)

omit [K.Normal] in
theorem tauBridge_def (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    hC.tauBridge i hj = ((dadeZMap hC.isDadeData
      ⟨h.primeTIbridge σ ζ δ 2 i j,
        primeTIbridge_mem_dadeZDomain hC.local_data hC.image_subset i hj⟩ :
    charSpanZero (Irr G)) : G → ℂ) := (rfl)

omit [K.Normal] in
theorem cfInner_self_tauBridge (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hC.tauBridge i hj) (hC.tauBridge i hj) = 6 := by
  rw [tauBridge, cfInner_dadeZMap, h.cfInner_self_primeTIbridge hC.local_data i hj]
  norm_num

omit [K.Normal] in
include hC in
theorem tauBridge_mem_virtualChars (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : hC.tauBridge i hj ∈ virtualChars G :=
  dadeZMap_mem_virtualChars hC.isDadeData _

noncomputable def nuOf (_hC : IsLargeLinearLayerData h σ ζ d δ A T ω P τ ν)
    {χ : ↥L → ℂ} (hχ : χ ∈ P) : G → ℂ :=
  (ν ⟨χ, Submodule.subset_span hχ⟩ : G → ℂ)

omit [K.Normal] in
theorem nuOf_def {χ : ↥L → ℂ} (hχ : χ ∈ P) :
    hC.nuOf hχ = (ν ⟨χ, Submodule.subset_span hχ⟩ : G → ℂ) := (rfl)

omit [K.Normal] in
include hC in
theorem nuOf_mem_virtualChars {χ : ↥L → ℂ} (hχ : χ ∈ P) : hC.nuOf hχ ∈ virtualChars G :=
  (ν ⟨χ, Submodule.subset_span hχ⟩).2

omit [K.Normal] in
include hC in
theorem cfInner_nuOf {χ ψ : ↥L → ℂ} (hχ : χ ∈ P) (hψ : ψ ∈ P) :
    cfInner (hC.nuOf hχ) (hC.nuOf hψ) = cfInner χ ψ := hC.coherent.inner_eq _ _

omit [K.Normal] in
include hC in
theorem cfInner_nuOf_eq_ite {χ ψ : ↥L → ℂ} (hχ : χ ∈ P) (hψ : ψ ∈ P) [Decidable (χ = ψ)] :
    cfInner (hC.nuOf hχ) (hC.nuOf hψ) = if χ = ψ then 1 else 0 := by
  rw [hC.cfInner_nuOf hχ hψ]
  by_cases hc : χ = ψ
  · subst hc; simp [cfInner_self_of_mem_Irr (hC.subset_Irr hχ)]
  · simp [hc, cfInner_eq_zero_of_mem_Irr (hC.subset_Irr hχ) (hC.subset_Irr hψ) hc]

omit [K.Normal] in
include hC in
theorem cfInner_self_nuOf {χ : ↥L → ℂ} (hχ : χ ∈ P) :
    cfInner (hC.nuOf hχ) (hC.nuOf hχ) = 1 := by
  rw [hC.cfInner_nuOf hχ hχ]; exact cfInner_self_of_mem_Irr (hC.subset_Irr hχ)

omit [K.Normal] in
include hC in
theorem sub_zeta_mem_charSpanZero {ξ : ↥L → ℂ} (hξ : ξ ∈ P) : ξ - ζ ∈ charSpanZero P := by
  refine mem_charSpanZero.2 ⟨sub_mem (Submodule.subset_span hξ)
    (Submodule.subset_span hC.zeta_mem), ?_⟩
  simp only [Pi.sub_apply, hC.degree_eq _ hξ, hC.degree_eq _ hC.zeta_mem, sub_self]

omit [K.Normal] in
include hC in
theorem nuOf_sub_nuOf_zeta {ξ : ↥L → ℂ} (hξ : ξ ∈ P) :
    hC.nuOf hξ - hC.nuOf hC.zeta_mem
      = (ν ⟨ξ - ζ, charSpanZero_le _ (hC.sub_zeta_mem_charSpanZero hξ)⟩ : G → ℂ) := by
  have hsplit : (⟨ξ - ζ, charSpanZero_le _ (hC.sub_zeta_mem_charSpanZero hξ)⟩ :
      Submodule.span ℤ P)
      = ⟨ξ, Submodule.subset_span hξ⟩ - ⟨ζ, Submodule.subset_span hC.zeta_mem⟩ := rfl
  rw [hsplit, map_sub, nuOf, nuOf, Submodule.coe_sub]

include hC in
theorem cfInner_tauBridge_nu (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    {f : ↥L → ℂ} (hf : f ∈ charSpanZero P) :
    cfInner (hC.tauBridge i hj) (ν ⟨f, charSpanZero_le _ hf⟩ : G → ℂ)
      = cfInner (h.primeTIbridge σ ζ δ 2 i j) f := by
  have hfZ : f ∈ dadeZDomain L A := hC.mem_dadeZDomain_of_mem_charSpanZero hf
  have hnu : (ν ⟨f, charSpanZero_le _ hf⟩ : G → ℂ)
      = ((dadeZMap hC.isDadeData ⟨f, hfZ⟩ : charSpanZero (Irr G)) : G → ℂ) := by
    rw [coe_dadeZMap]
    exact PartialCoherent.coe_nu_eq_dadeMap hC.isDadeData hC.coherent hC.tau_eq _
      ⟨f, mem_dadeDomain_of_mem_dadeZDomain hfZ⟩ rfl
  rw [tauBridge, hnu, cfInner_dadeZMap]

omit [K.Normal] in
include hC in
theorem cfInner_primeTIbridge_mem (i : Irr ↥W₁) (j : Irr ↥W₂) {ξ : ↥L → ℂ} (hξ : ξ ∈ P)
    [Decidable (ξ = ζ)] :
    cfInner (h.primeTIbridge σ ζ δ 2 i j) ξ = -2 * (if ξ = ζ then 1 else 0) := by
  have hKn := h.normal
  have hzero : ∀ k : Irr ↥W₂, cfInner (h.primeTIirr σ i k) ξ = 0 := by
    intro k
    have hkey := h.cfInner_primeTIirr_eq_zero_of_mem_indFam hC.local_data.isometry
      (indFam_mono K Set.sdiff_subset (hC.subset_indFam hξ)) (hC.subset_Irr hξ) i k
    rw [← conj_cfInner, hkey, map_zero]
  have hz : cfInner ζ ξ = (if ξ = ζ then 1 else 0) := by
    by_cases hc : ξ = ζ
    · subst hc; simp [cfInner_self_of_mem_Irr (hC.subset_Irr hξ)]
    · simp [hc, cfInner_eq_zero_of_mem_Irr (hC.subset_Irr hC.zeta_mem) (hC.subset_Irr hξ)
        (Ne.symm hc)]
  rw [h.cfInner_primeTIbridge_left, hzero j, hzero (principalIrr ↥W₂), hz]
  push_cast
  ring

include hC in
theorem cfInner_tauBridge_nuZeta (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hC.tauBridge i hj) (hC.nuOf hC.zeta_mem) = -2 := by
  classical
  have _ : Fintype ↑P := hC.finite_family.fintype
  obtain ⟨c, hc⟩ := exists_int_cfInner_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualChars (hC.tauBridge_mem_virtualChars i hj))
    (mem_span_Irr_of_mem_virtualChars (hC.nuOf_mem_virtualChars hC.zeta_mem))
  set a : ℤ := c + 2 with ha
  have hcoef : ∀ x : ↑P, cfInner (hC.tauBridge i hj) (hC.nuOf x.2)
      = ((a - 2 * (if (x : ↥L → ℂ) = ζ then 1 else 0) : ℤ) : ℂ) := by
    intro x
    have hsub := hC.cfInner_tauBridge_nu i hj (hC.sub_zeta_mem_charSpanZero x.2)
    rw [← hC.nuOf_sub_nuOf_zeta x.2, cfInner_sub_right, hc, cfInner_sub_right,
      hC.cfInner_primeTIbridge_mem i j x.2, h.cfInner_primeTIbridge_zeta hC.local_data i j] at hsub
    rw [ha]
    push_cast
    push_cast at hsub
    linear_combination hsub
  have hortho : ∀ x y : ↑P, cfInner (hC.nuOf x.2) (hC.nuOf y.2) = if x = y then 1 else 0 := by
    intro x y
    rw [hC.cfInner_nuOf_eq_ite x.2 y.2]
    exact if_congr Subtype.ext_iff.symm rfl rfl
  have hbessel := sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite hortho (hC.tauBridge i hj)
  rw [hC.cfInner_self_tauBridge i hj] at hbessel
  have hsumsq : ∑ x : ↑P, (a - 2 * (if (x : ↥L → ℂ) = ζ then 1 else 0)) ^ 2 ≤ 6 := by
    have h1 : ∀ x : ↑P, ‖cfInner (hC.tauBridge i hj) (hC.nuOf x.2)‖ ^ 2
        = (((a - 2 * (if (x : ↥L → ℂ) = ζ then 1 else 0) : ℤ) : ℝ)) ^ 2 := by
      intro x
      rw [hcoef x, Complex.norm_intCast, sq_abs]
    rw [Finset.sum_congr rfl fun x _ => h1 x] at hbessel
    have h2 : ((∑ x : ↑P, (a - 2 * (if (x : ↥L → ℂ) = ζ then 1 else 0)) ^ 2 : ℤ) : ℝ)
        ≤ ((6 : ℤ) : ℝ) := by
      push_cast
      simpa using hbessel
    exact_mod_cast h2
  have hsumsq' : ∑ x : ↑P,
      (a - 2 * (if x = (⟨ζ, hC.zeta_mem⟩ : ↑P) then 1 else 0)) ^ 2 ≤ 6 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) hsumsq
    have hiff : ((x : ↥L → ℂ) = ζ) ↔ (x = (⟨ζ, hC.zeta_mem⟩ : ↑P)) :=
      ⟨fun hh => Subtype.ext hh, fun hh => congrArg Subtype.val hh⟩
    rw [if_congr hiff rfl rfl]
  have hcard : 8 ≤ Fintype.card ↑P := by
    have hE := hC.eight_le
    rwa [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hE
  have ha0 : a = 0 := eq_zero_of_sum_sq_le_six (⟨ζ, hC.zeta_mem⟩ : ↑P) hcard hsumsq'
  have hcn : c = -2 := by omega
  rw [hc, hcn]
  norm_num

noncomputable def tauBridgeCorrected (hC : IsLargeLinearLayerData h σ ζ d δ A T ω P τ ν)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) : G → ℂ :=
  hC.tauBridge i hj + (2 : ℂ) • hC.nuOf hC.zeta_mem

omit [K.Normal] in
theorem tauBridgeCorrected_def (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    hC.tauBridgeCorrected i hj = hC.tauBridge i hj + (2 : ℂ) • hC.nuOf hC.zeta_mem := (rfl)

omit [K.Normal] in
include hC in
theorem tauBridgeCorrected_mem_virtualChars (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : hC.tauBridgeCorrected i hj ∈ virtualChars G := by
  rw [tauBridgeCorrected_def, show (2 : ℂ) • hC.nuOf hC.zeta_mem
    = (2 : ℤ) • hC.nuOf hC.zeta_mem from by
      rw [← Int.cast_smul_eq_zsmul ℂ (2 : ℤ) (hC.nuOf hC.zeta_mem)]; norm_num]
  exact add_mem (hC.tauBridge_mem_virtualChars i hj)
    (Submodule.smul_mem _ _ (hC.nuOf_mem_virtualChars hC.zeta_mem))

include hC in
theorem cfInner_self_tauBridgeCorrected (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hC.tauBridgeCorrected i hj) (hC.tauBridgeCorrected i hj) = 2 := by
  have hzn : cfInner (hC.nuOf hC.zeta_mem) (hC.tauBridge i hj) = -2 := by
    rw [← conj_cfInner, hC.cfInner_tauBridge_nuZeta i hj]
    simp [map_ofNat]
  rw [tauBridgeCorrected_def, cfInner_add_left, cfInner_add_right, cfInner_add_right,
    cfInner_smul_left, cfInner_smul_left, cfInner_smul_right, cfInner_smul_right,
    hC.cfInner_self_tauBridge i hj, hC.cfInner_tauBridge_nuZeta i hj, hzn,
    hC.cfInner_self_nuOf hC.zeta_mem]
  simp only [map_ofNat]
  ring

include hC in
theorem nuOf_zeta_apply_eq_zero_of_mem_cyclicTIDiff {v : G}
    (hv : v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)) :
    hC.nuOf hC.zeta_mem v = 0 := by
  have hW2K : W₂.map L.subtype ≤ K.map L.subtype := Subgroup.map_mono h.right_le
  have hW1K : W₁.map L.subtype ⊓ K.map L.subtype = ⊥ := by
    rw [← Subgroup.map_inf_eq W₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]
  exact PartialCoherent.nu_apply_eq_zero_of_mem_cyclicTIDiff hC.odd hC.isCyclicTIPair hW2K hW1K
    hC.omega_isometry hC.isDadeData hC.image_sdiff_subset hC.cyclicTIDiff_subset_param
    hC.subset_indFam hC.star_mem hC.coherent hC.tau_eq hC.zeta_mem
    (hC.subset_Irr hC.zeta_mem) hv

omit [K.Normal] in
include hC in
theorem tauBridge_apply_of_mem_cyclicTIDiff (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) {v : G}
    (hv : v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)) :
    hC.tauBridge i hj v = h.primeTIbridge σ ζ δ 2 i j
      ⟨v, hC.isDadeData.mem_of_mem (hC.cyclicTIDiff_subset_param hv)⟩ :=
  dadeZMap_apply_mem hC.isDadeData _ (hC.cyclicTIDiff_subset_param hv)

include hC in
theorem tauBridgeCorrected_apply_of_mem_cyclicTIDiff (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) (v : ↥((W₁ ⊔ W₂).map L.subtype))
    (hv : (v : G) ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype)) :
    hC.tauBridgeCorrected i hj (v : G)
      = (δ : ℂ) * (hC.isCyclicTIPair.prodChar
            ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
            ((irrMapSubtype L W₂ j : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v
          - hC.isCyclicTIPair.prodChar
            ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
            ((principalIrr ↥(W₂.map L.subtype) : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v) := by
  have hvL : (v : G) ∈ L := Subgroup.map_subtype_le _ v.2
  have humem : (⟨(v : G), hvL⟩ : ↥L) ∈ W₁ ⊔ W₂ := by
    obtain ⟨x, hx, hxv⟩ := v.2
    have hxe : (⟨(v : G), hvL⟩ : ↥L) = x := Subtype.ext hxv.symm
    rw [hxe]; exact hx
  set u : ↥(W₁ ⊔ W₂) := ⟨⟨(v : G), hvL⟩, humem⟩ with hu
  have hveq : mapSubtypeEquiv L (W₁ ⊔ W₂) u = v := Subtype.ext (by rw [coe_mapSubtypeEquiv])
  have huV : ((u : ↥L)) ∈ cyclicTIset W₁ W₂ := by
    rw [mem_cyclicTIset]
    obtain ⟨hvW, hv1, hv2⟩ := mem_cyclicTIDiff.1 hv
    exact ⟨u.2, fun hc => hv1 ⟨(u : ↥L), hc, rfl⟩, fun hc => hv2 ⟨(u : ↥L), hc, rfl⟩⟩
  rw [tauBridgeCorrected_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hC.nuOf_zeta_apply_eq_zero_of_mem_cyclicTIDiff hv, mul_zero, add_zero,
    hC.tauBridge_apply_of_mem_cyclicTIDiff i hj hv,
    show (⟨(v : G), hC.isDadeData.mem_of_mem (hC.cyclicTIDiff_subset_param hv)⟩ : ↥L)
      = ((u : ↥L)) from rfl,
    h.primeTIbridge_apply_of_mem_cyclicTIset hC.local_data i hj (v := u) huV]
  congr 2
  · rw [← hveq, prodChar_irrMapSubtype h.isCyclicTIPair hC.isCyclicTIPair]
  · rw [← irrMapSubtype_principal L W₂, ← hveq,
      prodChar_irrMapSubtype h.isCyclicTIPair hC.isCyclicTIPair]

include hC in
theorem tau_primeTIbridge_eq (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    hC.tauBridge i hj
      = (δ : ℂ) • (hC.isCyclicTIPair.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
          - hC.isCyclicTIPair.prodCharEta ω (irrMapSubtype L W₁ i)
              (principalIrr ↥(W₂.map L.subtype)))
        - (2 : ℂ) • hC.nuOf hC.zeta_mem := by
  have hne : (irrMapSubtype L W₁ i, irrMapSubtype L W₂ j)
      ≠ (irrMapSubtype L W₁ i, principalIrr ↥(W₂.map L.subtype)) := by
    intro hc
    have h2 : irrMapSubtype L W₂ j = principalIrr ↥(W₂.map L.subtype) := congrArg Prod.snd hc
    exact hj (irrMapSubtype_injective L W₂ (h2.trans (irrMapSubtype_principal L W₂).symm))
  have hkey := hC.isCyclicTIPair.eq_signed_sub_prodCharEta hC.omega_isometry hne
    (ε := (δ : ℂ)) (by rcases hC.local_data.sign with hd | hd <;> rw [hd] <;> norm_num)
    (mem_span_Irr_of_mem_virtualChars (hC.tauBridgeCorrected_mem_virtualChars i hj))
    (hC.cfInner_self_tauBridgeCorrected i hj)
    (fun v hv => hC.tauBridgeCorrected_apply_of_mem_cyclicTIDiff i hj v hv)
  rw [tauBridgeCorrected_def] at hkey
  rw [← hkey]
  abel

end IsLargeLinearLayerData

end LargeLinearLayer

end CFSG.FeitThompson

end
