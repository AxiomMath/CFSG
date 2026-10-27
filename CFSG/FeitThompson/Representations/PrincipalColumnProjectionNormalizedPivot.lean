module

import CFSG.FeitThompson.Representations.CoreCoherentIrreducibleArrayOrthogonality
public import CFSG.FeitThompson.Representations.CyclicTITwoColumnHalfSelection
public import CFSG.FeitThompson.Definitions.CoreDetectingNormalInducedFamily
public import CFSG.FeitThompson.Representations.CoherentFamilyCommonSignDegreeRatio
import CFSG.FeitThompson.Representations.OddBridgeProjectionRigidity
import CFSG.FeitThompson.Representations.CentralFamilyCoherentMapNormOneBridge
import CFSG.FeitThompson.Representations.DadeBetaIntegralDegreeZero
public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import CFSG.FeitThompson.Representations.NormalInducedFamilyWeightedNorm
import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.DegreeZeroNormalInductionsPuncturedSupport

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PrimeDadePivot

open scoped ComplexConjugate

section Pivot

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

theorem exists_apply_ne_apply_one_of_mem_Irr {X : Type*} [Group X] [Finite X] {θ : X → ℂ}
    (hθ : θ ∈ Irr X) (hne : θ ≠ 1) : ∃ x : X, θ x ≠ θ 1 := by
  have : Fintype X := Fintype.ofFinite X
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h0 : cfInner θ (1 : X → ℂ) = 0 := by
    rw [cfInner_eq_ite_of_mem_Irr hθ one_mem_Irr, if_neg hne]
  rw [cfInner_def] at h0
  have hsum : ∑ x : X, θ x * conj ((1 : X → ℂ) x) = (Nat.card X : ℂ) * θ 1 := by
    simp only [Pi.one_apply, map_one, mul_one]
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hcon x, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [hsum] at h0
  have hcpos : 0 < Nat.card X := Nat.card_pos
  have hcard : ((Nat.card X : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hcpos.ne'
  have h1 := apply_one_ne_zero_of_mem_Irr hθ
  field_simp at h0
  exact h1 h0

theorem indFam_sdiff_subset_indFamDetect_top (K : Subgroup L) :
    indFam K (Irr ↥K \ {1}) ⊆ indFamDetect K (⊤ : Subgroup ↥K) := by
  intro f hf
  obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam K).1 hf
  refine (mem_indFamDetect K).2 ⟨θ, mem_irrDetect.2 ⟨?_, ?_⟩, rfl⟩
  · rw [← Irr_eq_irrChar]; exact hθ
  · intro hsub
    obtain ⟨x, hx⟩ := exists_apply_ne_apply_one_of_mem_Irr hθ (by simpa using hθ1)
    exact hx (mem_charValueKernel.1 (hsub (by simp)))

open scoped Classical in
theorem exists_isCoherentWith_eq_sub_of_pivot
    {S1 : Set (L → ℂ)} (hS1Irr : S1 ⊆ Irr L) (hS1fin : S1.Finite) (hS1card : 2 ≤ S1.ncard)
    {ζ : L → ℂ} (hζ : ζ ∈ S1) (hdeg : ∀ χ ∈ S1, χ 1 = ζ 1)
    {τ : charSpanZero S1 →+ virtualChars G} {ν : Submodule.span ℤ S1 →+ virtualChars G}
    (hν : IsCoherentWith S1 τ ν)
    {P₀ ψ : G → ℂ} (hx : P₀ - ψ ∈ Submodule.span ℤ (Irr G))
    (hxx : cfInner (P₀ - ψ) (P₀ - ψ) = 1)
    (hpivot : ∀ χ : S1, χ ≠ ⟨ζ, hζ⟩ →
      cfInner (P₀ - ψ) (coherentVal ν ⟨ζ, hζ⟩ - coherentVal ν χ) = 1) :
    ∃ ν' : Submodule.span ℤ S1 →+ virtualChars G, IsCoherentWith S1 τ ν' ∧
      ψ = P₀ - coherentVal ν' ⟨ζ, hζ⟩ := by
  classical
  have hfin : Finite ↑S1 := hS1fin.to_subtype
  have hcard : 2 ≤ Nat.card ↑S1 := by rwa [Nat.card_coe_set_eq]
  have hmem : ∀ χ : S1, coherentVal ν χ ∈ Submodule.span ℤ (Irr G) := fun χ =>
    virtualChars_le_span_Irr (coherentVal_mem_virtualChars ν χ)
  have he : ∀ χ χ' : S1, cfInner (coherentVal ν χ) (coherentVal ν χ') = if χ = χ' then 1 else 0 :=
    cfInner_coherentVal_coherentVal hS1Irr hν
  have hrel : ∀ χ : S1, χ ≠ ⟨ζ, hζ⟩ →
      cfInner (P₀ - ψ) (coherentVal ν χ)
        = (((1 : ℤ) : ℂ)) * (cfInner (P₀ - ψ) (coherentVal ν ⟨ζ, hζ⟩) - 1) := by
    intro χ hχ
    have h := hpivot χ hχ
    rw [cfInner_sub_right] at h
    push_cast
    linear_combination -h
  rcases SibleyCentralAlignment.eq_pivot_or_exists_eq_neg (i₀ := ⟨ζ, hζ⟩) hcard hmem he hx hxx
      (b := fun _ => (1 : ℤ)) (fun _ => one_pos) hrel with hxeq | ⟨χ₁, hχ₁, huniq, -, hxeq⟩
  · exact ⟨ν, hν, by rw [← hxeq]; ring⟩
  · obtain ⟨μ, hμ, -, hμζ⟩ := SibleyCentralAlignment.exists_isCoherentWith_swap hS1Irr hS1fin hν
      hζ χ₁ hχ₁ huniq hdeg hxeq
    exact ⟨μ, hμ, by rw [hμζ]; ring⟩

end Pivot

section Column

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {ω : classFun ↥W →ₗ[ℂ] classFun G}

theorem cfInner_self_prodCharEtaColSum (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) (j : Irr ↥W2) :
    cfInner (hW.prodCharEtaColSum ω j) (hW.prodCharEtaColSum ω j) = (Nat.card ↥W1 : ℂ) := by
  have hfW1 := hW.finite_left
  have hcomm := hW.isMulCommutative_left
  have : Fintype ↑(Irr ↥W1) := Fintype.ofFinite _
  nth_rewrite 2 [hW.prodCharEtaColSum_eq_sum (σ := ω) j]
  rw [cfInner_sum_right]
  have hterm : ∀ i : Irr ↥W1, cfInner (hW.prodCharEtaColSum ω j) (hW.prodCharEta ω i j) = 1 :=
    fun i => by rw [hW.cfInner_prodCharEtaColSum_prodCharEta hω j i j, if_pos rfl]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
    card_Irr_eq_card_of_isMulCommutative]

theorem cfInner_self_prodCharEtaColSum_sub (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω) {ψ : G → ℂ}
    (hψnorm : cfInner ψ ψ = (Nat.card ↥W1 : ℂ) + 1)
    (hproj : ∀ (i : Irr ↥W1) (l : Irr ↥W2),
      IsOrthogonal (ψ - hW.prodCharEtaColSum ω (principalIrr ↥W2)) (hW.prodCharEta ω i l)) :
    cfInner (hW.prodCharEtaColSum ω (principalIrr ↥W2) - ψ)
      (hW.prodCharEtaColSum ω (principalIrr ↥W2) - ψ) = 1 := by
  have hPP := cfInner_self_prodCharEtaColSum hW hω (principalIrr ↥W2)
  have h0 : cfInner (hW.prodCharEtaColSum ω (principalIrr ↥W2))
      (ψ - hW.prodCharEtaColSum ω (principalIrr ↥W2)) = 0 :=
    hW.cfInner_prodCharEtaColSum_eq_zero _ hproj
  have h1 : cfInner (hW.prodCharEtaColSum ω (principalIrr ↥W2)) ψ = (Nat.card ↥W1 : ℂ) := by
    rw [cfInner_sub_right, hPP] at h0
    linear_combination h0
  have h2 : cfInner ψ (hW.prodCharEtaColSum ω (principalIrr ↥W2)) = (Nat.card ↥W1 : ℂ) := by
    rw [← conj_cfInner, h1]; simp
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hPP, h1, h2, hψnorm]
  ring

end Column

section Main

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K : Subgroup ↥L} [K.Normal] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {ω : classFun ↥W →ₗ[ℂ] classFun G} {A0 : Set G} {T : G → Subgroup G}
  {S1 : Set (↥L → ℂ)} {τ : charSpanZero S1 →+ virtualChars G}
  {ν : Submodule.span ℤ S1 →+ virtualChars G} {ζ : ↥L → ℂ}

omit [Fintype G] in
theorem mem_dadeDomain_of_mem_span_indFam
    (hA0 : ∀ x : ↥L, x ∈ K → x ≠ 1 → (x : G) ∈ A0)
    (hS1 : S1 ⊆ indFam K (Irr ↥K)) {f : ↥L → ℂ} (hf : f ∈ Submodule.span ℤ S1)
    (hf1 : f 1 = 0) : f ∈ dadeDomain L A0 := by
  refine mem_dadeDomain.2 ⟨NormalInducedFamily.mem_classFun_of_mem_span_indFam hS1 hf,
    fun x hx => ?_⟩
  by_cases hxK : x ∈ K
  · by_cases hx1 : x = 1
    · rw [hx1]; exact hf1
    · exact absurd (hA0 x hxK hx1) hx
  · exact NormalInducedFamily.eq_zero_of_mem_span_indFam_of_notMem K hS1 hf hxK

omit [Fintype G] in
theorem indClassFun_one_sub_mem_dadeDomain
    (hA0 : ∀ x : ↥L, x ∈ K → x ≠ 1 → (x : G) ∈ A0)
    (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) (hζ1 : ζ 1 = (K.index : ℂ)) :
    indClassFun K (1 : ↥K → ℂ) - ζ ∈ dadeDomain L A0 := by
  refine mem_dadeDomain_of_mem_span_indFam hA0 (S1 := indFam K (Irr ↥K)) (subset_refl _) ?_ ?_
  · exact sub_mem (Submodule.subset_span (NormalInducedFamily.indClassFun_one_mem_indFam K))
      (Submodule.subset_span (indFam_mono K Set.sdiff_subset hζS))
  · rw [Pi.sub_apply, NormalInducedWeightedNorm.indClassFun_one_apply_one, hζ1, sub_self]

theorem coe_nu_eq_coe_dadeMap (hD : IsDadeData L A0 T) (hν : IsCoherentWith S1 τ ν)
    (hτ : ∀ (f : charSpanZero S1) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (f : Submodule.span ℤ S1) (F : dadeDomain L A0) (h : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have h1 : (1 : G) ∉ A0 := fun hc => (hD.subset_sdiff hc).2 rfl
  have hF1 : (F : ↥L → ℂ) 1 = 0 := dadeDomain.apply_eq_zero F.2 (by simpa using h1)
  have hf0 : (f : ↥L → ℂ) ∈ charSpanZero S1 := mem_charSpanZero.2 ⟨f.2, by rw [h]; exact hF1⟩
  have hincl : f = Submodule.inclusion (charSpanZero_le S1) ⟨(f : ↥L → ℂ), hf0⟩ := Subtype.ext rfl
  rw [hincl, hν.eq_on_zero ⟨(f : ↥L → ℂ), hf0⟩]
  exact hτ ⟨(f : ↥L → ℂ), hf0⟩ F h

theorem cfInner_self_dadeMapFun_indClassFun_one_sub (hD : IsDadeData L A0 T)
    (hA0 : ∀ x : ↥L, x ∈ K → x ≠ 1 → (x : G) ∈ A0)
    (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) (hζIrr : ζ ∈ Irr ↥L) (hζ1 : ζ 1 = (K.index : ℂ)) :
    cfInner (dadeMapFun L A0 T (indClassFun K (1 : ↥K → ℂ) - ζ))
      (dadeMapFun L A0 T (indClassFun K (1 : ↥K → ℂ) - ζ)) = (K.index : ℂ) + 1 := by
  rw [← coe_dadeMap hD ⟨indClassFun K (1 : ↥K → ℂ) - ζ,
      indClassFun_one_sub_mem_dadeDomain hA0 hζS hζ1⟩, cfInner_self_dadeMap hD]
  exact NormalInducedFamily.cfInner_self_indClassFun_one_sub hζS hζIrr

omit [Fintype G] in
theorem dadeMapFun_indClassFun_one_sub_mem_span_Irr [Finite G] (hD : IsDadeData L A0 T)
    (hA0 : ∀ x : ↥L, x ∈ K → x ≠ 1 → (x : G) ∈ A0)
    (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) (hζ1 : ζ 1 = (K.index : ℂ)) :
    dadeMapFun L A0 T (indClassFun K (1 : ↥K → ℂ) - ζ) ∈ Submodule.span ℤ (Irr G) := by
  rw [← coe_dadeMap hD ⟨indClassFun K (1 : ↥K → ℂ) - ζ,
      indClassFun_one_sub_mem_dadeDomain hA0 hζS hζ1⟩]
  exact hD.dadeMap_mem_span_Irr _ (NormalInducedFamily.indClassFun_one_sub_mem_span_Irr hζS)

omit [Fintype G] in
theorem cfInner_indClassFun_one_sub_sub
    (hS1 : S1 ⊆ indFam K (Irr ↥K \ {1})) (hS1Irr : S1 ⊆ Irr ↥L)
    (hζ : ζ ∈ S1) {χ : ↥L → ℂ} (hχ : χ ∈ S1) (hne : χ ≠ ζ) :
    cfInner (indClassFun K (1 : ↥K → ℂ) - ζ) (ζ - χ) = -1 := by
  have key : ∀ ξ ∈ S1, cfInner (indClassFun K (1 : ↥K → ℂ)) ξ = 0 := by
    intro ξ hξ
    obtain ⟨θ, ⟨hθ, hθ1⟩, hθeq⟩ := (mem_indFam K).1 (hS1 hξ)
    have h := NormalInducedFamily.cfInner_indClassFun_indClassFun_one K hθ (by simpa using hθ1)
    rw [← conj_cfInner] at h
    rw [← hθeq]
    simpa using h
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, key ζ hζ, key χ hχ,
    cfInner_self_of_mem_Irr (hS1Irr hζ),
    cfInner_eq_zero_of_mem_Irr (hS1Irr hζ) (hS1Irr hχ) (Ne.symm hne)]
  ring

theorem cfInner_dadeMapFun_coherentVal_sub (hD : IsDadeData L A0 T)
    (hA0 : ∀ x : ↥L, x ∈ K → x ≠ 1 → (x : G) ∈ A0)
    (hS1 : S1 ⊆ indFam K (Irr ↥K \ {1})) (hS1Irr : S1 ⊆ Irr ↥L)
    (hdeg : ∀ χ ∈ S1, χ 1 = (K.index : ℂ)) (hν : IsCoherentWith S1 τ ν)
    (hτ : ∀ (f : charSpanZero S1) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hζ : ζ ∈ S1) {χ : ↥L → ℂ} (hχ : χ ∈ S1) (hne : χ ≠ ζ) :
    cfInner (dadeMapFun L A0 T (indClassFun K (1 : ↥K → ℂ) - ζ))
      (coherentVal ν ⟨ζ, hζ⟩ - coherentVal ν ⟨χ, hχ⟩) = -1 := by
  have hz : ζ - χ ∈ charSpanZero S1 := sub_mem_charSpanZero hdeg hζ hχ
  have hzD : ζ - χ ∈ dadeDomain L A0 :=
    mem_dadeDomain_of_mem_span_indFam hA0 (hS1.trans (indFam_mono K Set.sdiff_subset))
      (charSpanZero_le S1 hz) (mem_charSpanZero.1 hz).2
  have hbase : (τ ⟨ζ - χ, hz⟩ : G → ℂ) = coherentVal ν ⟨ζ, hζ⟩ - coherentVal ν ⟨χ, hχ⟩ :=
    SibleyCentralAlignment.coe_baseline_sub hν hζ hχ hz
  rw [← hbase, hτ _ ⟨ζ - χ, hzD⟩ rfl, ← coe_dadeMap hD ⟨indClassFun K (1 : ↥K → ℂ) - ζ,
    indClassFun_one_sub_mem_dadeDomain hA0 (hS1 hζ) (hdeg ζ hζ)⟩, cfInner_dadeMap hD]
  exact cfInner_indClassFun_one_sub_sub hS1 hS1Irr hζ hχ hne

theorem cfInner_prodCharEtaColSum_coherentVal_eq_zero
    (hodd : Odd (Nat.card G)) (hW : IsCyclicTIPair W W1 W2)
    (hW2 : W2 ≤ K.map L.subtype) (hW1 : W1 ⊓ K.map L.subtype = ⊥)
    (hω : IsCyclicTIIsometry W W1 W2 ω) (hD : IsDadeData L A0 T)
    (hVA : cyclicTIDiff W W1 W2 ⊆ A0)
    (hA0 : ∀ x : ↥L, x ∈ K → x ≠ 1 → (x : G) ∈ A0)
    (hS1 : S1 ⊆ indFam K (Irr ↥K \ {1})) (hS1Irr : S1 ⊆ Irr ↥L)
    (hS1star : ∀ χ ∈ S1, star χ ∈ S1) (hν : IsCoherentWith S1 τ ν)
    (hτ : ∀ (f : charSpanZero S1) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (j : Irr ↥W2) (χ : S1) :
    cfInner (hW.prodCharEtaColSum ω j) (coherentVal ν χ) = 0 := by
  refine hW.cfInner_prodCharEtaColSum_eq_zero _ fun i l => ?_
  rw [coherentVal_apply]
  exact CoherentCore.isOrthogonal_nu_prodCharEta hodd hW hW2 hW1 hω hD hVA
    (hS1.trans (indFam_sdiff_subset_indFamDetect_top K)) hS1star hν.inner_eq
    (fun f x hx => dadeDomain.apply_eq_zero (mem_dadeDomain_of_mem_span_indFam hA0
      (hS1.trans (indFam_mono K Set.sdiff_subset)) (charSpanZero_le S1 f.2)
      (charSpanZero_apply_one f)) hx)
    (coe_nu_eq_coe_dadeMap hD hν hτ) χ.2 (hS1Irr χ.2) i l

theorem exists_isCoherentWith_eq_prodCharEtaColSum_sub
    (hodd : Odd (Nat.card G)) (hW : IsCyclicTIPair W W1 W2)
    (hW2 : W2 ≤ K.map L.subtype) (hW1 : W1 ⊓ K.map L.subtype = ⊥)
    (hω : IsCyclicTIIsometry W W1 W2 ω) (hD : IsDadeData L A0 T)
    (hVA : cyclicTIDiff W W1 W2 ⊆ A0)
    (hA0 : ∀ x : ↥L, x ∈ K → x ≠ 1 → (x : G) ∈ A0)
    (hm : K.index = Nat.card ↥W1)
    (hS1 : S1 ⊆ indFam K (Irr ↥K \ {1})) (hS1Irr : S1 ⊆ Irr ↥L)
    (hS1star : ∀ χ ∈ S1, star χ ∈ S1) (hS1card : 2 ≤ S1.ncard)
    (hdeg : ∀ χ ∈ S1, χ 1 = (K.index : ℂ))
    (hζ : ζ ∈ S1) (hν : IsCoherentWith S1 τ ν)
    (hτ : ∀ (f : charSpanZero S1) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hproj : ∀ (i : Irr ↥W1) (l : Irr ↥W2),
      IsOrthogonal (dadeMapFun L A0 T (indClassFun K (1 : ↥K → ℂ) - ζ)
        - hW.prodCharEtaColSum ω (principalIrr ↥W2)) (hW.prodCharEta ω i l)) :
    ∃ ν' : Submodule.span ℤ S1 →+ virtualChars G, IsCoherentWith S1 τ ν' ∧
      dadeMapFun L A0 T (indClassFun K (1 : ↥K → ℂ) - ζ)
        = hW.prodCharEtaColSum ω (principalIrr ↥W2) - coherentVal ν' ⟨ζ, hζ⟩ := by
  classical
  set ψ : G → ℂ := dadeMapFun L A0 T (indClassFun K (1 : ↥K → ℂ) - ζ) with hψdef
  set P₀ : G → ℂ := hW.prodCharEtaColSum ω (principalIrr ↥W2) with hP₀def
  have hζS : ζ ∈ indFam K (Irr ↥K \ {1}) := hS1 hζ
  have hζ1 : ζ 1 = (K.index : ℂ) := hdeg ζ hζ
  have hS1fin : S1.Finite := (indFam_finite K (finite_Irr.subset Set.sdiff_subset)).subset hS1
  have hψnorm : cfInner ψ ψ = (Nat.card ↥W1 : ℂ) + 1 := by
    rw [hψdef, cfInner_self_dadeMapFun_indClassFun_one_sub hD hA0 hζS (hS1Irr hζ) hζ1, hm]
  have hx : P₀ - ψ ∈ Submodule.span ℤ (Irr G) :=
    sub_mem (hW.prodCharEtaColSum_mem_span_Irr hω _)
      (dadeMapFun_indClassFun_one_sub_mem_span_Irr hD hA0 hζS hζ1)
  have hxx : cfInner (P₀ - ψ) (P₀ - ψ) = 1 :=
    cfInner_self_prodCharEtaColSum_sub hW hω hψnorm hproj
  have hpivot : ∀ χ : S1, χ ≠ ⟨ζ, hζ⟩ →
      cfInner (P₀ - ψ) (coherentVal ν ⟨ζ, hζ⟩ - coherentVal ν χ) = 1 := by
    intro χ hχ
    have hχne : (χ : ↥L → ℂ) ≠ ζ := fun he => hχ (Subtype.ext he)
    have h1 : cfInner ψ (coherentVal ν ⟨ζ, hζ⟩ - coherentVal ν χ) = -1 := by
      simpa using cfInner_dadeMapFun_coherentVal_sub hD hA0 hS1 hS1Irr hdeg hν hτ hζ χ.2 hχne
    have h2 : cfInner P₀ (coherentVal ν ⟨ζ, hζ⟩ - coherentVal ν χ) = 0 := by
      rw [cfInner_sub_right,
        cfInner_prodCharEtaColSum_coherentVal_eq_zero hodd hW hW2 hW1 hω hD hVA hA0 hS1 hS1Irr
          hS1star hν hτ _ ⟨ζ, hζ⟩,
        cfInner_prodCharEtaColSum_coherentVal_eq_zero hodd hW hW2 hW1 hω hD hVA hA0 hS1 hS1Irr
          hS1star hν hτ _ χ, sub_zero]
    rw [cfInner_sub_left, h1, h2]
    ring
  exact exists_isCoherentWith_eq_sub_of_pivot hS1Irr hS1fin hS1card hζ
    (fun χ hχ => by rw [hdeg χ hχ, hζ1]) hν hx hxx hpivot

end Main

end PrimeDadePivot

end CFSG.FeitThompson

namespace CFSG.FeitThompson

end CFSG.FeitThompson

end
