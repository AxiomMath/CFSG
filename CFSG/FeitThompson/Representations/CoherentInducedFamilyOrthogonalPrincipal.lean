module

public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.DadeReciprocityAveraging
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.DegreeZeroNormalInductionsPuncturedSupport
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open ComplexConjugate

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {R : G → Subgroup G}
  {H : Subgroup ↥L}

theorem coe_mem_iff_mem_and_ne_one
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1})) (x : ↥L) :
    (x : G) ∈ A ↔ x ∈ H ∧ x ≠ 1 := by
  rw [hA]
  constructor
  · rintro ⟨y, ⟨hyH, hy1⟩, hyx⟩
    obtain rfl : y = x := Subtype.ext hyx
    exact ⟨hyH, by simpa using hy1⟩
  · rintro ⟨hxH, hx1⟩
    exact ⟨x, ⟨hxH, by simpa using hx1⟩, rfl⟩

theorem mem_classFun_of_mem_span_indFam [Fintype ↥L] {X : Set (↥H → ℂ)} {S : Set (↥L → ℂ)}
    (hS : S ⊆ indFam H X) {f : ↥L → ℂ} (hf : f ∈ Submodule.span ℤ S) : f ∈ classFun ↥L := by
  have h : Submodule.span ℤ S ≤ (classFun ↥L).restrictScalars ℤ := by
    rw [Submodule.span_le]
    intro g hg
    exact mem_classFun.2 fun x y hxy => by
      obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
      exact (conj_eq_of_mem_indFam H (hS hg) c x).symm
  exact h hf

theorem mem_dadeDomain_of_mem_span_indFam [Fintype ↥L] [H.Normal]
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1})) {S : Set (↥L → ℂ)}
    (hS : S ⊆ indFam H (Irr ↥H)) {f : ↥L → ℂ}
    (hf : f ∈ Submodule.span ℤ S) (hf1 : f 1 = 0) : f ∈ dadeDomain L A := by
  refine mem_dadeDomain.2 ⟨mem_classFun_of_mem_span_indFam hS hf, fun x hx => ?_⟩
  by_cases hxH : x ∈ H
  · have hx1 : x = 1 := by
      by_contra h
      exact hx ((coe_mem_iff_mem_and_ne_one hA x).2 ⟨hxH, h⟩)
    rw [hx1, hf1]
  · exact eq_zero_of_mem_span_indFam_of_notMem H hS hf hxH

theorem cfInner_dadeMap_one [Fintype G] [Fintype ↥L] (hD : IsDadeData L A R)
    (F : dadeDomain L A) :
    cfInner ((dadeMap hD F : classFun G) : G → ℂ) (1 : G → ℂ)
      = cfInner ((F : ↥L → ℂ)) (1 : ↥L → ℂ) := by
  rw [cfInner_dadeMap_eq_cfInner_dadeAverage hD F (one_mem_classFun G), cfInner_def, cfInner_def]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : (y : G) ∈ A
  · rw [show dadeAverage A R (1 : G → ℂ) (y : G) = 1 from
      dadeAverage_apply_of_eq_on hy fun _ _ => rfl]
    simp
  · rw [dadeDomain.apply_eq_zero F.2 hy, zero_mul, zero_mul]

theorem cfInner_one_of_mem_indFam_sdiff [Fintype ↥L] {ξ : ↥L → ℂ}
    (hξ : ξ ∈ indFam H (Irr ↥H \ {1})) : cfInner ξ (1 : ↥L → ℂ) = 0 := by
  obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam H).1 hξ
  exact cfInner_indClassFun_one H hθ hθ1

theorem cfInner_one_one {X : Type*} [Group X] [Fintype X] :
    cfInner (1 : X → ℂ) (1 : X → ℂ) = 1 :=
  cfInner_self_of_mem_Irr one_mem_Irr

section Main

variable [Fintype G] [Fintype ↥L] [H.Normal] {S : Set (↥L → ℂ)} {ζ : ↥L → ℂ}
  {ν : Submodule.span ℤ S →+ Submodule.span ℤ (Irr G)}
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : S = indFam H (Irr ↥H \ {1}))
  (hνiso : ∀ f h : Submodule.span ℤ S,
    cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) (hζ1 : ζ 1 = (H.index : ℂ))

omit [Fintype G] [H.Normal] in
include hS in
theorem subset_indFam_Irr : S ⊆ indFam H (Irr ↥H) := hS ▸ indFam_mono H Set.sdiff_subset

private theorem natCast_zsmul_eq (m : ℕ) {α : Type*} [AddCommGroup α] [Module ℂ α] (v : α) :
    (m : ℤ) • v = (m : ℂ) • v := by
  rw [← Int.cast_smul_eq_zsmul ℂ (m : ℤ) v]
  norm_num

include hD hA hS hντ hζS hζ1 in
theorem exists_cfInner_one_eq_mul {ξ : ↥L → ℂ} (hξ : ξ ∈ S) :
    ∃ m : ℕ, 0 < m ∧
      cfInner (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) (1 : G → ℂ)
        = (m : ℂ) * cfInner (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) (1 : G → ℂ) := by
  have hSsub : S ⊆ indFam H (Irr ↥H) := subset_indFam_Irr hS
  obtain ⟨d, hd0, hdvd, hd1⟩ := exists_apply_one_eq_of_mem_indFam H (hSsub hξ)
  obtain ⟨m, rfl⟩ := hdvd
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.mul_zero] at hd0; exact absurd hd0 (lt_irrefl 0)
    · exact h
  refine ⟨m, hm0, ?_⟩
  set x : Submodule.span ℤ S := ⟨ξ, Submodule.subset_span hξ⟩ with hxdef
  set z : Submodule.span ℤ S := ⟨ζ, Submodule.subset_span hζS⟩ with hzdef
  set g : Submodule.span ℤ S := x - (m : ℤ) • z with hgdef
  have hgcoe : (g : ↥L → ℂ) = ξ - (m : ℂ) • ζ := by
    have h1 : (g : ↥L → ℂ) = (x : ↥L → ℂ) - (m : ℤ) • (z : ↥L → ℂ) := by
      rw [hgdef]; rfl
    rw [h1, natCast_zsmul_eq]
  have hg1 : (g : ↥L → ℂ) 1 = 0 := by
    rw [hgcoe]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd1, hζ1]
    push_cast
    ring
  have hFmem : (g : ↥L → ℂ) ∈ dadeDomain L A :=
    mem_dadeDomain_of_mem_span_indFam hA hSsub g.2 hg1
  have hzero : cfInner (ν g : G → ℂ) (1 : G → ℂ) = 0 := by
    rw [hντ g ⟨(g : ↥L → ℂ), hFmem⟩ rfl, cfInner_dadeMap_one hD ⟨(g : ↥L → ℂ), hFmem⟩, hgcoe,
      cfInner_sub_left, cfInner_smul_left, cfInner_one_of_mem_indFam_sdiff (hS ▸ hξ),
      cfInner_one_of_mem_indFam_sdiff (hS ▸ hζS)]
    ring
  have hνg : (ν g : G → ℂ) = (ν x : G → ℂ) - (m : ℂ) • (ν z : G → ℂ) := by
    have h1 : (ν g : G → ℂ) = (ν x : G → ℂ) - (m : ℤ) • (ν z : G → ℂ) := by
      rw [hgdef, map_sub, map_zsmul]; rfl
    rw [h1, natCast_zsmul_eq]
  rw [hνg, cfInner_sub_left, cfInner_smul_left, sub_eq_zero] at hzero
  exact hzero

include hD hA hS hνiso hντ hζS hζIrr hζ1 in
theorem cfInner_one_eq_zero_of_eq (hS2 : S.Nontrivial) :
    cfInner (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) (1 : G → ℂ) = 0 := by
  have hSsub : S ⊆ indFam H (Irr ↥H) := subset_indFam_Irr hS
  set z : Submodule.span ℤ S := ⟨ζ, Submodule.subset_span hζS⟩ with hzdef
  have hnorm : cfInner (ν z : G → ℂ) (ν z : G → ℂ) = 1 := by
    rw [hνiso z z]
    exact cfInner_self_of_mem_Irr hζIrr
  have hsign := mem_Irr_or_neg_mem_Irr_of_mem_span_Irr_of_cfInner_self_eq_one (ν z).2 hnorm
  obtain ⟨ξ, hξS, hξζ⟩ : ∃ ξ ∈ S, ξ ≠ ζ := by
    obtain ⟨a, ha, b, hb, hab⟩ := hS2
    by_cases h : a = ζ
    · exact ⟨b, hb, fun hb' => hab (by rw [h, ← hb'])⟩
    · exact ⟨a, ha, h⟩
  set x : Submodule.span ℤ S := ⟨ξ, Submodule.subset_span hξS⟩ with hxdef
  have horth : cfInner (ν x : G → ℂ) (ν z : G → ℂ) = 0 := by
    rw [hνiso x z]
    exact cfInner_eq_zero_of_mem_indFam H (hSsub hξS) (hSsub hζS) hξζ
  obtain ⟨m, hm0, hratio⟩ := exists_cfInner_one_eq_mul hD hA hS hντ hζS hζ1 hξS
  have hmne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm0.ne'
  rcases hsign with hIrr | hIrr
  ·
    have hne1 : (ν z : G → ℂ) ≠ 1 := by
      intro h1
      rw [h1] at horth
      rw [h1, cfInner_one_one] at hratio
      rw [hratio, mul_one] at horth
      exact hmne horth
    exact cfInner_eq_zero_of_mem_Irr hIrr one_mem_Irr hne1
  ·
    have hne1 : -(ν z : G → ℂ) ≠ 1 := by
      intro h1
      have h2 : (ν z : G → ℂ) = -1 := by rw [← h1]; ring
      rw [h2] at horth
      rw [h2, cfInner_neg_left, cfInner_one_one] at hratio
      rw [cfInner_neg_right, hratio] at horth
      simp only [mul_neg, mul_one, neg_neg] at horth
      exact hmne horth
    have h0 : cfInner (-(ν z : G → ℂ)) (1 : G → ℂ) = 0 :=
      cfInner_eq_zero_of_mem_Irr hIrr one_mem_Irr hne1
    rw [cfInner_neg_left, neg_eq_zero] at h0
    exact h0

include hD hA hS hνiso hντ hζS hζIrr hζ1 in
theorem cfInner_one_eq_zero_of_mem_indFam_sdiff (hS2 : S.Nontrivial) {ξ : ↥L → ℂ} (hξ : ξ ∈ S) :
    cfInner (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) (1 : G → ℂ) = 0 := by
  obtain ⟨m, -, hratio⟩ := exists_cfInner_one_eq_mul hD hA hS hντ hζS hζ1 hξ
  rw [hratio, cfInner_one_eq_zero_of_eq hD hA hS hνiso hντ hζS hζIrr hζ1 hS2, mul_zero]

include hD hA hS hνiso hντ hζS hζIrr hζ1 in
theorem isOrthogonal_one_of_mem_indFam_sdiff (hS2 : S.Nontrivial) {ξ : ↥L → ℂ} (hξ : ξ ∈ S) :
    IsOrthogonal (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) (1 : G → ℂ) :=
  isOrthogonal_iff.2
    (cfInner_one_eq_zero_of_mem_indFam_sdiff hD hA hS hνiso hντ hζS hζIrr hζ1 hS2 hξ)

end Main

end NormalInducedFamily

end CFSG.FeitThompson
