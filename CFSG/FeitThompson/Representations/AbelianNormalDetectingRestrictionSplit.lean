module

public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
public import CFSG.FeitThompson.Definitions.CoreDetectingNormalInducedFamily
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.ProjectedRestrictionGenChars
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
import CFSG.FeitThompson.Representations.NormalInductionPreservesKernelSubgroup
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

theorem Irr.apply_one_eq_one_of_isMulCommutative {A : Type*} [Group A] [IsMulCommutative A]
    {θ : A → ℂ} (hθ : θ ∈ Irr A) : θ 1 = 1 := by
  obtain ⟨V, hirr, rfl⟩ := mem_Irr.1 hθ
  have hi : Representation.IsIrreducible V.ρ := hirr
  rw [FDRep.char_one, Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative V.ρ]
  norm_num

theorem sum_irrFinset_apply_eq_zero {A : Type*} [Group A] [IsMulCommutative A] [Finite A]
    {x : A} (hx : x ≠ 1) : ∑ θ ∈ irrFinset A, θ x = 0 := by
  have h := congrFun (leftRegular_character_eq_sum (G := A)) x
  rw [leftRegular_character_of_ne_one hx, Finset.sum_apply] at h
  have h2 : ∀ θ : irrFinset A, (((θ : A → ℂ) 1) • (θ : A → ℂ)) x = (θ : A → ℂ) x := fun θ => by
    rw [Pi.smul_apply, Irr.apply_one_eq_one_of_isMulCommutative (mem_irrFinset.1 θ.2), one_smul]
  rw [Finset.sum_congr rfl fun θ _ => h2 θ,
    Finset.sum_coe_sort (irrFinset A) (fun θ : A → ℂ => θ x)] at h
  exact h.symm

theorem exists_intCast_finsetSum_of_mem_span_Irr {X : Type*} [Group X] [Fintype X] {f : X → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr X)) :
    ∃ m : (X → ℂ) → ℤ, f = ∑ θ ∈ irrFinset X, (m θ : ℂ) • θ ∧
      ∀ θ ∈ irrFinset X, cfInner f θ = (m θ : ℂ) := by
  classical
  have : Fintype (Irr X) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := mem_span_Irr_iff_exists_intCast_sum.1 hf
  refine ⟨fun θ => if h : θ ∈ Irr X then n ⟨θ, h⟩ else 0, ?_, ?_⟩
  · rw [Finset.sum_subtype (irrFinset X) (fun _ => mem_irrFinset)
      (fun θ : X → ℂ => ((if h : θ ∈ Irr X then n ⟨θ, h⟩ else 0 : ℤ) : ℂ) • θ), hn]
    exact Finset.sum_congr rfl fun θ _ => by rw [dif_pos θ.2]
  · intro θ hθ
    rw [mem_irrFinset] at hθ
    change cfInner f θ = ((if h : θ ∈ Irr X then n ⟨θ, h⟩ else 0 : ℤ) : ℂ)
    rw [dif_pos hθ, hn]
    exact cfInner_intCast_sum_Irr_coe n ⟨θ, hθ⟩

theorem resClassFun_eq_cfInner_self_smul_sum {L : Type*} [Group L] [Fintype L] {H : Subgroup L}
    [H.Normal] {ζ : L → ℂ} (hζ : ζ ∈ indFam H (Irr ↥H)) :
    resClassFun H ζ
      = cfInner ζ ζ • ∑ θ ∈ {θ ∈ irrFinset ↥H | indClassFun H θ = ζ}, θ := by
  classical
  have : Fintype (Irr ↥H) := Fintype.ofFinite _
  have hcf : ζ ∈ classFun L := by
    obtain ⟨θζ, -, rfl⟩ := (mem_indFam H).1 hζ; exact indClassFun_mem_classFun H θζ
  have step : resClassFun H ζ
      = ∑ θ ∈ irrFinset ↥H, (if indClassFun H θ = ζ then cfInner ζ ζ • θ else 0) := by
    rw [eq_sum_cfInner_smul_of_mem_classFun (resClassFun_mem_classFun H hcf),
      Finset.sum_subtype (irrFinset ↥H) (fun _ => mem_irrFinset)
        (fun θ : ↥H → ℂ => if indClassFun H θ = ζ then cfInner ζ ζ • θ else 0)]
    refine Finset.sum_congr rfl fun θ _ => ?_
    by_cases h : indClassFun H ((θ : Irr ↥H) : ↥H → ℂ) = ζ
    · rw [if_pos h]
      congr 1
      rw [← conj_cfInner, ← cfInner_indClassFun H _ hcf, h, conj_cfInner]
    · rw [if_neg h, ← conj_cfInner, ← cfInner_indClassFun H _ hcf,
        NormalInducedFamily.cfInner_eq_zero_of_mem_indFam H
          (indClassFun_mem_indFam H θ.2) hζ h, map_zero, zero_smul]
  rw [step, Finset.sum_filter, Finset.smul_sum]
  refine Finset.sum_congr rfl fun θ _ => ?_
  by_cases h : indClassFun H θ = ζ
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, smul_zero]

section Detect

variable {G : Type*} [Group G] {S : Subgroup G} [Fintype ↥S] {H P : Subgroup ↥S}

theorem exists_mem_Irr_of_mem_indFamDetect {ζ : ↥S → ℂ}
    (hζ : ζ ∈ indFamDetect H (P.subgroupOf H)) :
    ∃ θ ∈ Irr ↥H, ¬ ((P.subgroupOf H : Set ↥H) ⊆ charValueKernel θ) ∧ indClassFun H θ = ζ := by
  obtain ⟨θ, hθ, hind⟩ := (mem_indFamDetect H).1 hζ
  obtain ⟨hθ1, hθ2⟩ := mem_irrDetect.1 hθ
  exact ⟨θ, by rw [← irrChar_eq_Irr]; exact hθ1, hθ2, hind⟩

theorem indClassFun_mem_indFamDetect_iff [P.Normal] (hPH : P ≤ H) {θ : ↥H → ℂ}
    (hθ : θ ∈ Irr ↥H) :
    indClassFun H θ ∈ indFamDetect H (P.subgroupOf H) ↔
      ¬ ((P.subgroupOf H : Set ↥H) ⊆ charValueKernel θ) := by
  have key : ∀ {ψ : ↥H → ℂ}, ψ ∈ Irr ↥H →
      ((P : Set ↥S) ⊆ charValueKernel (indClassFun H ψ) ↔
        (P.subgroupOf H : Set ↥H) ⊆ charValueKernel ψ) := by
    intro ψ hψ
    rw [← normalInduction_indClassFun_eq]
    exact NormalInduction.subset_charValueKernel_indClassFun_iff hPH
      (by rw [normalInduction_irrChars_eq_Irr]; exact hψ)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨θ', hθ', hind⟩ := (mem_indFamDetect H).1 h
    have hθ'Irr : θ' ∈ Irr ↥H := by rw [← irrChar_eq_Irr]; exact (mem_irrDetect.1 hθ').1
    rw [← key hθ, ← hind, key hθ'Irr]
    exact (mem_irrDetect.1 hθ').2
  · exact indClassFun_mem_indFamDetect H
      (mem_irrDetect.2 ⟨by rw [irrChar_eq_Irr]; exact hθ, h⟩)

theorem apply_one_eq_index_of_mem_indFamDetect [IsMulCommutative ↥H] {ζ : ↥S → ℂ}
    (hζ : ζ ∈ indFamDetect H (P.subgroupOf H)) : ζ 1 = (H.index : ℂ) := by
  obtain ⟨θ, hθ, -, rfl⟩ := exists_mem_Irr_of_mem_indFamDetect hζ
  rw [indClassFun_apply_one, Irr.apply_one_eq_one_of_isMulCommutative hθ, mul_one]

theorem mem_indFam_Irr_of_mem_indFamDetect {ζ : ↥S → ℂ}
    (hζ : ζ ∈ indFamDetect H (P.subgroupOf H)) : ζ ∈ indFam H (Irr ↥H) := by
  have := indFamDetect_subset_indFam_irrChar H (P.subgroupOf H) hζ
  rwa [irrChar_eq_Irr] at this

theorem exists_pos_cfInner_self_of_mem_indFamDetect [H.Normal] {ζ : ↥S → ℂ}
    (hζ : ζ ∈ indFamDetect H (P.subgroupOf H)) : ∃ k : ℕ, 0 < k ∧ cfInner ζ ζ = (k : ℂ) := by
  obtain ⟨θ, hθ, -, rfl⟩ := exists_mem_Irr_of_mem_indFamDetect hζ
  exact ⟨H.relIndex (inertiaGroup H θ),
    Nat.pos_of_ne_zero (NormalInducedFamily.relIndex_inertiaGroup_ne_zero H θ),
    cfInner_self_indClassFun H hθ⟩

theorem resClassFun_resClassFun_mem_span_Irr [Finite G] {χ : G → ℂ}
    (hχ : χ ∈ Submodule.span ℤ (Irr G)) :
    resClassFun H (resClassFun S χ) ∈ Submodule.span ℤ (Irr ↥H) := by
  have h := comp_mem_span_Irr (X := ↥H) (S.subtype.comp H.subtype) hχ
  have he : χ ∘ (S.subtype.comp H.subtype) = resClassFun H (resClassFun S χ) := by
    funext x; simp
  rwa [he] at h

theorem exists_intCast_eq_on_sdiff_one_of_cfInner_eq_zero
    [Fintype G] [H.Normal] [P.Normal] [IsMulCommutative ↥H] (hPH : P ≤ H)
    (ν : Submodule.span ℤ (indFamDetect H (P.subgroupOf H)) →+ Submodule.span ℤ (Irr G))
    (hν : ∀ f : charSpanZero (indFamDetect H (P.subgroupOf H)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = indClassFun S (f : ↥S → ℂ))
    (hcard : 2 ≤ (indFamDetect H (P.subgroupOf H)).ncard)
    {ζ : ↥S → ℂ} (hζ : ζ ∈ indFamDetect H (P.subgroupOf H))
    {χ : G → ℂ} (hχ : χ ∈ Submodule.span ℤ (Irr G))
    (horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect H (P.subgroupOf H), ξ ≠ ζ →
      cfInner (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) χ = 0) :
    ∃ (a : ℤ) (n : ℕ) (b : (↥H → ℂ) → ℤ), 0 < n ∧
      cfInner (ν ⟨ζ, Submodule.subset_span hζ⟩ : G → ℂ) χ = (a : ℂ) ∧
      cfInner ζ ζ = (n : ℂ) ∧ ζ 1 = (H.index : ℂ) ∧
      (∀ θ, ¬ ((P.subgroupOf H : Set ↥H) ⊆ charValueKernel θ) → b θ = 0) ∧
      ∀ x : ↥H, x ≠ 1 → χ ((x : ↥S) : G) = ((a : ℂ) / (n : ℂ)) * ζ (x : ↥S)
        + ∑ θ ∈ irrFinset ↥H, (b θ : ℂ) * θ x := by
  classical
  have hfH : Fintype ↥H := Fintype.ofFinite _
  have hχcf : χ ∈ classFun G := mem_classFun_of_mem_span_Irr hχ
  obtain ⟨m, hmsum, hmcf⟩ := exists_intCast_finsetSum_of_mem_span_Irr
    (resClassFun_resClassFun_mem_span_Irr (H := H) hχ)
  obtain ⟨a, ha⟩ := exists_int_cfInner_of_mem_span_Irr
    (ν ⟨ζ, Submodule.subset_span hζ⟩).2 hχ
  obtain ⟨n, hnpos, hn⟩ := exists_pos_cfInner_self_of_mem_indFamDetect hζ
  obtain ⟨ξ₀, hξ₀T, hξ₀ne⟩ := Set.exists_ne_of_one_lt_ncard hcard ζ
  obtain ⟨θ₀, hθ₀, hθ₀det, hθ₀ind⟩ := exists_mem_Irr_of_mem_indFamDetect hξ₀T
  set b : (↥H → ℂ) → ℤ := fun θ =>
    if (P.subgroupOf H : Set ↥H) ⊆ charValueKernel θ then m θ - m θ₀ else 0 with hb
  refine ⟨a, n, b, hnpos, ha, hn, apply_one_eq_index_of_mem_indFamDetect hζ,
    fun θ hθ => by simp only [hb, if_neg hθ], ?_⟩
  have hfrob : ∀ θ ∈ irrFinset ↥H,
      cfInner (indClassFun H θ) (resClassFun S χ) = (m θ : ℂ) := by
    intro θ hθ
    rw [cfInner_indClassFun H _ (resClassFun_mem_classFun S hχcf), ← conj_cfInner, hmcf θ hθ]
    simp
  have hdiff : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect H (P.subgroupOf H),
      cfInner (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) χ
          - cfInner (ν ⟨ξ₀, Submodule.subset_span hξ₀T⟩ : G → ℂ) χ
        = cfInner (ξ - ξ₀) (resClassFun S χ) := by
    intro ξ hξ
    have h1 : (ξ - ξ₀) 1 = 0 := by
      rw [Pi.sub_apply, apply_one_eq_index_of_mem_indFamDetect hξ,
        apply_one_eq_index_of_mem_indFamDetect hξ₀T, sub_self]
    have hmem : ξ - ξ₀ ∈ charSpanZero (indFamDetect H (P.subgroupOf H)) :=
      mem_charSpanZero.2 ⟨sub_mem (Submodule.subset_span hξ) (Submodule.subset_span hξ₀T), h1⟩
    have hkey : (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ)
        - (ν ⟨ξ₀, Submodule.subset_span hξ₀T⟩ : G → ℂ) = indClassFun S (ξ - ξ₀) := by
      rw [← hν ⟨ξ - ξ₀, hmem⟩,
        show Submodule.inclusion (charSpanZero_le (indFamDetect H (P.subgroupOf H)))
            ⟨ξ - ξ₀, hmem⟩
          = (⟨ξ, Submodule.subset_span hξ⟩ :
              Submodule.span ℤ (indFamDetect H (P.subgroupOf H)))
            - ⟨ξ₀, Submodule.subset_span hξ₀T⟩ from Subtype.ext rfl, map_sub]
      rfl
    rw [← cfInner_sub_left, hkey, cfInner_indClassFun S _ hχcf]
  have hdetect : ∀ θ ∈ irrFinset ↥H, ¬ ((P.subgroupOf H : Set ↥H) ⊆ charValueKernel θ) →
      (m θ : ℂ) = (m θ₀ : ℂ) + (if indClassFun H θ = ζ then (a : ℂ) else 0) := by
    intro θ hθ hdet
    have hθIrr : θ ∈ Irr ↥H := mem_irrFinset.1 hθ
    have hξ : indClassFun H θ ∈ indFamDetect H (P.subgroupOf H) :=
      (indClassFun_mem_indFamDetect_iff hPH hθIrr).2 hdet
    have hd := hdiff (indClassFun H θ) hξ
    rw [horth ξ₀ hξ₀T hξ₀ne, sub_zero, cfInner_sub_left, hfrob θ hθ, ← hθ₀ind,
      hfrob θ₀ (mem_irrFinset.2 hθ₀)] at hd
    by_cases hzeta : indClassFun H θ = ζ
    · rw [if_pos hzeta]
      have hval : cfInner (ν ⟨indClassFun H θ, Submodule.subset_span hξ⟩ : G → ℂ) χ = (a : ℂ) := by
        subst hzeta; convert ha using 3
      rw [hval] at hd
      linear_combination -hd
    · rw [if_neg hzeta, add_zero]
      rw [horth _ hξ hzeta] at hd
      linear_combination -hd
  have hcoef : ∀ θ ∈ irrFinset ↥H, (m θ : ℂ)
      = (b θ : ℂ) + (m θ₀ : ℂ) + (if indClassFun H θ = ζ then (a : ℂ) else 0) := by
    intro θ hθ
    by_cases hdet : (P.subgroupOf H : Set ↥H) ⊆ charValueKernel θ
    · have hne : indClassFun H θ ≠ ζ := by
        intro h
        exact ((indClassFun_mem_indFamDetect_iff hPH (mem_irrFinset.1 hθ)).1 (h ▸ hζ)) hdet
      simp only [hb, if_pos hdet, if_neg hne]
      push_cast
      ring
    · simp only [hb, if_neg hdet]
      rw [hdetect θ hθ hdet]
      push_cast
      ring
  intro x hx
  have hres : χ ((x : ↥S) : G) = ∑ θ ∈ irrFinset ↥H, (m θ : ℂ) * θ x := by
    have h := congrFun hmsum x
    rw [resClassFun_apply, resClassFun_apply, Finset.sum_apply] at h
    simpa using h
  have hzero : ∑ θ ∈ irrFinset ↥H, θ x = 0 := sum_irrFinset_apply_eq_zero hx
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hζsum : ∑ θ ∈ irrFinset ↥H, (if indClassFun H θ = ζ then (1 : ℂ) else 0) * θ x
      = ζ (x : ↥S) / (n : ℂ) := by
    have h := congrFun (resClassFun_eq_cfInner_self_smul_sum
      (mem_indFam_Irr_of_mem_indFamDetect hζ)) x
    rw [resClassFun_apply, hn, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at h
    have hfilt : ∑ θ ∈ irrFinset ↥H, (if indClassFun H θ = ζ then (1 : ℂ) else 0) * θ x
        = ∑ θ ∈ {θ ∈ irrFinset ↥H | indClassFun H θ = ζ}, θ x := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun θ _ => ?_
      by_cases hh : indClassFun H θ = ζ
      · rw [if_pos hh, if_pos hh, one_mul]
      · rw [if_neg hh, if_neg hh, zero_mul]
    rw [hfilt, eq_div_iff hnne, mul_comm]
    exact h.symm
  rw [hres, Finset.sum_congr rfl (g := fun θ : ↥H → ℂ =>
    ((b θ : ℂ) + (m θ₀ : ℂ) + (if indClassFun H θ = ζ then (a : ℂ) else 0)) * θ x)
    fun θ hθ => by rw [hcoef θ hθ]]
  have expand : ∑ θ ∈ irrFinset ↥H,
        ((b θ : ℂ) + (m θ₀ : ℂ) + (if indClassFun H θ = ζ then (a : ℂ) else 0)) * θ x
      = ∑ θ ∈ irrFinset ↥H, (b θ : ℂ) * θ x
        + (m θ₀ : ℂ) * ∑ θ ∈ irrFinset ↥H, θ x
        + (a : ℂ) * ∑ θ ∈ irrFinset ↥H,
            (if indClassFun H θ = ζ then (1 : ℂ) else 0) * θ x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    by_cases h : indClassFun H θ = ζ
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  rw [expand, hzero, hζsum, mul_zero, add_zero]
  field_simp
  ring

end Detect

end CFSG.FeitThompson
