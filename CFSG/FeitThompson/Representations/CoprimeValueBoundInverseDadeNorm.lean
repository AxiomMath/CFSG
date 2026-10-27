module

public import CFSG.FeitThompson.Representations.CoherentReferenceImageOddNonzeroOffCore
public import CFSG.FeitThompson.Representations.DadeIntegerParameterNormBounds
public import CFSG.FeitThompson.Representations.DadePacketInverseNormBound
import CFSG.FeitThompson.Representations.CoherentInducedImageVanishesMixedTI
import CFSG.FeitThompson.Representations.DadeInverseConstantOffExceptionalFamily
import CFSG.FeitThompson.Representations.PrimeDadePrincipalRowSmallComplement
import CFSG.FeitThompson.Representations.OddArrayCoefficientsSupportingDegree

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Sets

variable {G : Type*} [Group G] {L : Subgroup G}

def puncturedCoreSet (K : Subgroup ↥L) : Set G :=
  (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})

theorem puncturedCoreSet_def (K : Subgroup ↥L) :
    puncturedCoreSet K = (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) := (rfl)

theorem mem_puncturedCoreSet {K : Subgroup ↥L} {g : G} :
    g ∈ puncturedCoreSet (G := G) K ↔ ∃ x : ↥L, (x ∈ K ∧ x ≠ 1) ∧ (x : G) = g := by
  simp [puncturedCoreSet]

theorem ncard_puncturedCoreSet (K : Subgroup ↥L) [Finite ↥L] :
    (puncturedCoreSet (G := G) K).ncard = Nat.card ↥K - 1 := by
  rw [puncturedCoreSet, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_sdiff_singleton_of_mem (by exact K.one_mem), ← Nat.card_coe_set_eq]
  rfl

def coprimeExceptionSet (K W₁ : Subgroup ↥L) (T : G → Subgroup G) : Set G :=
  {g | g ∉ totalDadeSupport (puncturedCoreSet K) T ∧ ¬ (orderOf g).Coprime (Nat.card ↥W₁)}

theorem mem_coprimeExceptionSet {K W₁ : Subgroup ↥L} {T : G → Subgroup G} {g : G} :
    g ∈ coprimeExceptionSet K W₁ T ↔
      g ∉ totalDadeSupport (puncturedCoreSet K) T ∧ ¬ (orderOf g).Coprime (Nat.card ↥W₁) :=
  Iff.rfl

theorem coprime_of_notMem_union_coprimeExceptionSet {K W₁ : Subgroup ↥L} {T : G → Subgroup G}
    {g : G} (hg : g ∉ totalDadeSupport (puncturedCoreSet K) T ∪ coprimeExceptionSet K W₁ T) :
    (orderOf g).Coprime (Nat.card ↥W₁) := by
  by_contra hc
  exact hg (Or.inr ⟨fun hmem => hg (Or.inl hmem), hc⟩)

end Sets

theorem one_sub_sub_inv_lt_of_le {m hh b : ℝ} (hm : 0 < m) (hh0 : 0 < hh)
    (hle : 1 - m / hh ≤ (hh - 1) / (hh * m) + b) : 1 - b - 1 / m < m / hh := by
  have hsplit : (hh - 1) / (hh * m) = 1 / m - 1 / (hh * m) := by field_simp
  have hpos : 0 < 1 / (hh * m) := by positivity
  rw [hsplit] at hle
  linarith

namespace IsUniformBridgeCoherenceData

open CrossFamilyProjection (coherentImage coherentImage_apply)
open NormalInducedFamily (nonprincipalBaselineHom coe_nonprincipalBaselineHom)

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ζ : ↥L → ℂ} {d n δ : ℤ} {A : Set G} {T : G → Subgroup G}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G}
  (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν)

section Enum

variable (K)

private def famEnum : ↑(indFam K (Irr ↥K \ {1})) → (↥L → ℂ) := Subtype.val

omit [Fintype G] [K.Normal] in
private theorem famEnum_apply (x : ↑(indFam K (Irr ↥K \ {1}))) :
    famEnum K x = (x : ↥L → ℂ) := rfl

omit [Fintype G] [K.Normal] in
private theorem range_famEnum : Set.range (famEnum K) = indFam K (Irr ↥K \ {1}) :=
  Subtype.range_coe

omit [Fintype G] [K.Normal] in
private theorem injective_famEnum : Function.Injective (famEnum K) := Subtype.val_injective

omit [Fintype G] [K.Normal] in
private theorem span_range_famEnum_le :
    Submodule.span ℤ (Set.range (famEnum K)) ≤ Submodule.span ℤ (indFam K (Irr ↥K \ {1})) :=
  le_of_eq (by rw [range_famEnum])

omit [Fintype G] [K.Normal] in
private theorem charSpanZero_range_famEnum_le :
    charSpanZero (Set.range (famEnum K)) ≤ charSpanZero (indFam K (Irr ↥K \ {1})) :=
  le_of_eq (by rw [range_famEnum])

private noncomputable def famNu (ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G) :
    Submodule.span ℤ (Set.range (famEnum K)) →+ virtualChars G :=
  ν.comp (Submodule.inclusion (span_range_famEnum_le K)).toAddMonoidHom

omit [Fintype G] [K.Normal] in
private theorem coe_famNu (ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G)
    (f : Submodule.span ℤ (Set.range (famEnum K))) :
    (famNu K ν f : G → ℂ) = (ν ⟨(f : ↥L → ℂ), span_range_famEnum_le K f.2⟩ : G → ℂ) := rfl

private noncomputable def famTau {A' : Set G} (hDB : IsDadeData L A' T)
    (hA' : A' = (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) :
    charSpanZero (Set.range (famEnum K)) →+ virtualChars G :=
  (nonprincipalBaselineHom hDB hA').comp
    (Submodule.inclusion (charSpanZero_range_famEnum_le K)).toAddMonoidHom

private theorem coe_famTau {A' : Set G} (hDB : IsDadeData L A' T)
    (hA' : A' = (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}))
    (f : charSpanZero (Set.range (famEnum K))) (F : dadeDomain L A')
    (hF : (F : ↥L → ℂ) = (f : ↥L → ℂ)) :
    (famTau K hDB hA' f : G → ℂ) = ((dadeMap hDB F : classFun G) : G → ℂ) :=
  coe_nonprincipalBaselineHom hDB hA' _ F hF

end Enum

include hC in
theorem isDadeData_puncturedCoreSet : IsDadeData L (puncturedCoreSet (G := G) K) T :=
  isDadeData_puncturedCore hC.isDadeData hC.image_puncturedCore_subset

include hC in
private theorem isCoherentWith_famNu :
    IsCoherentWith (Set.range (famEnum K))
      (famTau K hC.isDadeData_puncturedCoreSet rfl) (famNu K ν) where
  inner_eq f g := hC.nu_inner _ _
  eq_on_zero f := by
    refine Subtype.ext ?_
    have hsub : indFam K (Irr ↥K \ {1}) ⊆ indFam K (Irr ↥K) := indFam_mono K Set.sdiff_subset
    have hf0 : (f : ↥L → ℂ) ∈ charSpanZero (indFam K (Irr ↥K \ {1})) :=
      charSpanZero_range_famEnum_le K f.2
    have hmem : (f : ↥L → ℂ) ∈ dadeDomain L (puncturedCoreSet (G := G) K) :=
      NormalInducedFamily.mem_dadeDomain_of_mem_span_indFam rfl hsub
        (charSpanZero_le _ hf0) (charSpanZero_apply_one f)
    have h2 : ((famTau K hC.isDadeData_puncturedCoreSet rfl f : virtualChars G) : G → ℂ)
        = ((dadeMap hC.isDadeData_puncturedCoreSet ⟨(f : ↥L → ℂ), hmem⟩ : classFun G) : G → ℂ) :=
      coe_famTau K hC.isDadeData_puncturedCoreSet rfl f _ rfl
    rw [coe_famNu, h2]
    exact coe_nu_eq_dadeMap_puncturedCore hC.isDadeData hC.image_puncturedCore_subset
      hC.nu_eq_tau _ _ rfl

private def famZetaIdx (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν) :
    ↑(indFam K (Irr ↥K \ {1})) := ⟨ζ, hC.local_data.mem_indFam⟩

include hC in
private theorem coherentImage_famZetaIdx :
    coherentImage (famEnum K) (famNu K ν) hC.famZetaIdx = hC.nuZeta := by
  have := h.isCyclicTIPair.finite_left
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  rw [coherentImage_apply, coe_famNu, hC.nuZeta_def]
  congr 1

include hC in
theorem one_sub_div_le_re_cfInner_self_dadeAverage_nuZeta
    (hbound : 2 * Nat.card ↥W₁ + 1 ≤ Nat.card ↥K) :
    1 - (Nat.card ↥W₁ : ℝ) / (Nat.card ↥K : ℝ)
      ≤ (cfInner (fun y : ↥L => dadeAverage (puncturedCoreSet K) T hC.nuZeta (y : G))
          (fun y : ↥L => dadeAverage (puncturedCoreSet K) T hC.nuZeta (y : G))).re := by
  have hidx : K.index = Nat.card ↥W₁ := h.index_eq
  have hdeg : famEnum K hC.famZetaIdx 1 = (K.index : ℂ) := by
    change ζ 1 = (K.index : ℂ)
    rw [hC.local_data.apply_one, hidx]
  have key := NormalInducedFamily.one_sub_index_div_card_le_cfInner_self_dadeAverage_coherentImage
    (H := K) (ξ := famEnum K) (ν := famNu K ν) (k₀ := hC.famZetaIdx)
    hC.isDadeData_puncturedCoreSet rfl (range_famEnum K) (injective_famEnum K)
    hC.isCoherentWith_famNu
    (fun f F hfF => coe_famTau K hC.isDadeData_puncturedCoreSet rfl f F hfF.symm)
    hC.local_data.mem_Irr hdeg
    (by rw [range_famEnum]; exact hC.nontrivial_indFam) (by rw [hidx]; exact hbound)
  rw [hC.coherentImage_famZetaIdx, hidx] at key
  exact key

include hC in
theorem nuZeta_mem_classFun : hC.nuZeta ∈ classFun G :=
  mem_classFun_of_mem_span_Irr (mem_span_Irr_of_mem_virtualChars hC.nuZeta_mem_virtualChars)

include hC in
theorem re_cfInner_self_dadeAverage_nuZeta_le :
    (cfInner (fun y : ↥L => dadeAverage (puncturedCoreSet K) T hC.nuZeta (y : G))
        (fun y : ↥L => dadeAverage (puncturedCoreSet K) T hC.nuZeta (y : G))).re
      ≤ ((Nat.card ↥K : ℝ) - 1) / (Nat.card ↥L : ℝ)
        + ((coprimeExceptionSet K W₁ T).ncard : ℝ) / (Nat.card G : ℝ) := by
  have hKpos : 1 ≤ Nat.card ↥K := Nat.card_pos
  have key := cfInner_self_dadeAverage_le_add_of_one_le_norm_sq
    hC.isDadeData_puncturedCoreSet (coprimeExceptionSet K W₁ T)
    ⟨hC.nuZeta, hC.nuZeta_mem_classFun⟩ hC.cfInner_self_nuZeta
    (fun g hg => by
      have hgD : g ∉ totalDadeSupport (puncturedCoreSet (G := G) K) T := fun hmem =>
        hg (Or.inl hmem)
      have hone : 1 ≤ ‖hC.nuZeta g‖ := hC.one_le_norm_nuZeta_apply hgD
        (coprime_of_notMem_union_coprimeExceptionSet hg)
      have h2 : (1 : ℝ) ≤ ‖hC.nuZeta g‖ ^ 2 := one_le_pow₀ hone
      exact h2)
  rw [show ((puncturedCoreSet (G := G) K).ncard : ℂ) / (Nat.card ↥L : ℂ)
        + ((coprimeExceptionSet K W₁ T).ncard : ℂ) / (Nat.card G : ℂ)
      = ((((Nat.card ↥K : ℝ) - 1) / (Nat.card ↥L : ℝ)
        + ((coprimeExceptionSet K W₁ T).ncard : ℝ) / (Nat.card G : ℝ) : ℝ) : ℂ) from by
      rw [ncard_puncturedCoreSet K]
      push_cast [Nat.cast_sub hKpos]
      ring,
    NormalInducedFamily.cfInner_self_eq_ofReal_re] at key
  exact Complex.real_le_real.1 key

include hC in
theorem one_sub_sub_inv_lt_div (hbound : 2 * Nat.card ↥W₁ + 1 ≤ Nat.card ↥K) :
    1 - ((coprimeExceptionSet K W₁ T).ncard : ℝ) / (Nat.card G : ℝ)
        - 1 / (Nat.card ↥W₁ : ℝ)
      < (Nat.card ↥W₁ : ℝ) / (Nat.card ↥K : ℝ) := by
  have hmpos : (0 : ℝ) < (Nat.card ↥W₁ : ℝ) := by exact_mod_cast Nat.card_pos (α := ↥W₁)
  have hhpos : (0 : ℝ) < (Nat.card ↥K : ℝ) := by exact_mod_cast Nat.card_pos (α := ↥K)
  have hcard : (Nat.card ↥L : ℝ) = (Nat.card ↥K : ℝ) * (Nat.card ↥W₁ : ℝ) := by
    have hK := K.card_mul_index
    rw [h.index_eq] at hK
    exact_mod_cast hK.symm
  have hlow := hC.one_sub_div_le_re_cfInner_self_dadeAverage_nuZeta hbound
  have hup := hC.re_cfInner_self_dadeAverage_nuZeta_le
  rw [hcard] at hup
  exact one_sub_sub_inv_lt_of_le hmpos hhpos (hlow.trans hup)

end IsUniformBridgeCoherenceData

end CFSG.FeitThompson

end
