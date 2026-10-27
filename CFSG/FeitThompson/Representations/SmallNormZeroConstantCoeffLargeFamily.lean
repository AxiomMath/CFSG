module

import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace EqualDegreeFamily

open ComplexConjugate
open scoped ComplexOrder

section Projection

variable {G : Type*} [Fintype G]

theorem card_mul_mul_conj_le_cfInner_self {ι : Type*} [Fintype ι] {η : ι → G → ℂ}
    (hone : ∀ i, cfInner (η i) (η i) = 1) (hzero : ∀ i j, i ≠ j → cfInner (η i) (η j) = 0)
    {f : G → ℂ} {c : ℂ} (hc : ∀ i, cfInner f (η i) = c) :
    (Fintype.card ι : ℂ) * (c * conj c) ≤ cfInner f f := by
  classical
  set P : G → ℂ := ∑ i, c • η i with hP
  have hPj : ∀ j, cfInner P (η j) = c := by
    intro j
    rw [hP, cfInner_sum_left, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [cfInner_smul_left, hone j, mul_one]
    · intro i _ hij
      rw [cfInner_smul_left, hzero i j hij, mul_zero]
  have hsub : ∀ j, cfInner (f - P) (η j) = 0 := fun j => by
    rw [cfInner_sub_left, hc j, hPj j, sub_self]
  have h1 : cfInner (f - P) P = 0 := by
    rw [hP, cfInner_sum_right]
    exact Finset.sum_eq_zero fun i _ => by rw [cfInner_smul_right, hsub i, mul_zero]
  have h2 : cfInner P (f - P) = 0 := by rw [← conj_cfInner, h1, map_zero]
  have hPP : cfInner P P = (Fintype.card ι : ℂ) * (c * conj c) := by
    conv_lhs => rw [hP]
    rw [cfInner_sum_left]
    have hterm : ∀ i : ι, cfInner (c • η i) P = c * conj c := fun i => by
      rw [cfInner_smul_left, ← conj_cfInner, hPj i]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsplit : cfInner f f = cfInner P P + cfInner (f - P) (f - P) := by
    have hs : P + (f - P) = f := add_sub_cancel _ _
    calc cfInner f f = cfInner (P + (f - P)) (P + (f - P)) := by rw [hs]
      _ = _ := by rw [cfInner_add_left, cfInner_add_right, cfInner_add_right, h1, h2]; ring
  rw [hsplit, ← hPP]
  simpa using cfInner_self_nonneg (f - P)

end Projection

variable {L G : Type*} [Group L] [Group G] {T : Finset (L → ℂ)} {e : ℂ}

theorem sub_mem_charSpanZero (hdeg : ∀ χ ∈ T, χ 1 = e) {χ ψ : L → ℂ} (hχ : χ ∈ T) (hψ : ψ ∈ T) :
    χ - ψ ∈ charSpanZero (T : Set (L → ℂ)) :=
  mem_charSpanZero.2
    ⟨Submodule.sub_mem _ (Submodule.subset_span (Finset.mem_coe.2 hχ))
      (Submodule.subset_span (Finset.mem_coe.2 hψ)), by simp [hdeg _ hχ, hdeg _ hψ]⟩

abbrev spanElt {χ : L → ℂ} (hχ : χ ∈ T) : Submodule.span ℤ (T : Set (L → ℂ)) :=
  ⟨χ, Submodule.subset_span (Finset.mem_coe.2 hχ)⟩

variable [Fintype L] [Fintype G] {D : Submodule ℤ (L → ℂ)}
  {hD0 : charSpanZero (T : Set (L → ℂ)) ≤ D}
  {τ : D →+ Submodule.span ℤ (Irr G)}
  {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ Submodule.span ℤ (Irr G)}

theorem cfInner_tau_nu_eq (hdeg : ∀ χ ∈ T, χ 1 = e)
    (hτ : ∀ f h : D, cfInner (τ f : G → ℂ) (τ h : G → ℂ) = cfInner (f : L → ℂ) (h : L → ℂ))
    (hντ : ∀ f : charSpanZero (T : Set (L → ℂ)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ)
        = (τ (Submodule.inclusion hD0 f) : G → ℂ))
    {α : D} (hα : ∀ χ ∈ T, cfInner (α : L → ℂ) χ = 0)
    {χ ψ : L → ℂ} (hχ : χ ∈ T) (hψ : ψ ∈ T) :
    cfInner (τ α : G → ℂ) (ν (spanElt hχ) : G → ℂ)
      = cfInner (τ α : G → ℂ) (ν (spanElt hψ) : G → ℂ) := by
  set f : charSpanZero (T : Set (L → ℂ)) :=
    ⟨χ - ψ, sub_mem_charSpanZero hdeg hχ hψ⟩ with hf
  have hincl : Submodule.inclusion (charSpanZero_le (T : Set (L → ℂ))) f
      = spanElt hχ - spanElt hψ := Subtype.ext rfl
  have h2 : cfInner (τ α : G → ℂ) (τ (Submodule.inclusion hD0 f) : G → ℂ) = 0 := by
    rw [hτ α (Submodule.inclusion hD0 f)]
    change cfInner (α : L → ℂ) (χ - ψ) = 0
    rw [cfInner_sub_right, hα _ hχ, hα _ hψ, sub_zero]
  rw [← hντ f, hincl, map_sub] at h2
  have h3 : ((ν (spanElt hχ) - ν (spanElt hψ) : Submodule.span ℤ (Irr G)) : G → ℂ)
      = (ν (spanElt hχ) : G → ℂ) - (ν (spanElt hψ) : G → ℂ) := rfl
  rw [h3, cfInner_sub_right, sub_eq_zero] at h2
  exact h2

theorem cfInner_tau_nu_eq_zero {Q : Finset (L → ℂ)} (hQT : Q ⊆ T) (hQIrr : ∀ χ ∈ Q, χ ∈ Irr L)
    (hdeg : ∀ χ ∈ T, χ 1 = e)
    (hτ : ∀ f h : D, cfInner (τ f : G → ℂ) (τ h : G → ℂ) = cfInner (f : L → ℂ) (h : L → ℂ))
    (hν : ∀ f h : Submodule.span ℤ (T : Set (L → ℂ)),
      cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : L → ℂ) (h : L → ℂ))
    (hντ : ∀ f : charSpanZero (T : Set (L → ℂ)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ)
        = (τ (Submodule.inclusion hD0 f) : G → ℂ))
    {α : D} (hα : ∀ χ ∈ T, cfInner (α : L → ℂ) χ = 0)
    (hcard : (cfInner (α : L → ℂ) (α : L → ℂ)).re < Q.card)
    {χ : L → ℂ} (hχ : χ ∈ T) :
    cfInner (τ α : G → ℂ) (ν (spanElt hχ) : G → ℂ) = 0 := by
  classical
  set c : ℂ := cfInner (τ α : G → ℂ) (ν (spanElt hχ) : G → ℂ) with hc
  set η : Q → G → ℂ := fun q => (ν (spanElt (hQT q.2)) : G → ℂ) with hη
  have hqq : ∀ q q' : Q, cfInner (η q) (η q') = if (q : L → ℂ) = (q' : L → ℂ) then 1 else 0 := by
    intro q q'
    rw [hη, hν]
    have h := cfInner_coe_Irr (G := L) ⟨(q : L → ℂ), hQIrr _ q.2⟩ ⟨(q' : L → ℂ), hQIrr _ q'.2⟩
    simp only [Subtype.mk.injEq] at h
    exact h
  have hone : ∀ q : Q, cfInner (η q) (η q) = 1 := fun q => by rw [hqq q q, if_pos rfl]
  have hzero : ∀ q q' : Q, q ≠ q' → cfInner (η q) (η q') = 0 := fun q q' hne => by
    rw [hqq q q', if_neg fun h => hne (Subtype.ext h)]
  have hceq : ∀ q : Q, cfInner (τ α : G → ℂ) (η q) = c := fun q => by
    rw [hc]; exact cfInner_tau_nu_eq (hD0 := hD0) hdeg hτ hντ hα (hQT q.2) hχ
  have hbound := card_mul_mul_conj_le_cfInner_self hone hzero hceq
  rw [hτ α α] at hbound
  have hcardQ : (Fintype.card Q : ℂ) = (Q.card : ℂ) := by simp
  rw [hcardQ] at hbound
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr (τ α).2 (ν (spanElt hχ)).2
  rw [← hc] at hm
  have hcc : c * conj c = ((m ^ 2 : ℤ) : ℂ) := by rw [hm]; push_cast; simp [sq]
  rw [hcc] at hbound
  have hb2 : (((Q.card : ℤ) * m ^ 2 : ℤ) : ℂ) ≤ cfInner (α : L → ℂ) (α : L → ℂ) := by
    push_cast
    push_cast at hbound
    exact hbound
  have hre : (((Q.card : ℤ) * m ^ 2 : ℤ) : ℝ) ≤ (cfInner (α : L → ℂ) (α : L → ℂ)).re := by
    have h := (Complex.le_def.1 hb2).1
    rwa [Complex.intCast_re] at h
  have hltZ : (Q.card : ℤ) * m ^ 2 < (Q.card : ℤ) := by
    have h2 : (((Q.card : ℤ) * m ^ 2 : ℤ) : ℝ) < ((Q.card : ℤ) : ℝ) := by
      push_cast at hre ⊢; linarith
    exact_mod_cast h2
  have hm0 : m = 0 := by nlinarith [sq_nonneg m, sq_nonneg (m - 1), sq_nonneg (m + 1)]
  rw [hm, hm0]
  simp

end EqualDegreeFamily

end CFSG.FeitThompson
