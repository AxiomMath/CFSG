module

public import CFSG.FeitThompson.Representations.InverseDadeInducedBasisExpansion
public import CFSG.FeitThompson.Representations.DadeBetaIntegralDegreeZero
public import CFSG.FeitThompson.Representations.DadeIntegerIsometry
import CFSG.FeitThompson.Representations.NormalInducedFamilyWeightedNorm
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open ComplexConjugate

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {A : Set G} {R : G → Subgroup G} {H : Subgroup ↥L} {S : Set (↥L → ℂ)}
  {χ : G → ℂ} {ζ : ↥L → ℂ}

omit [Fintype G] in
theorem indFam_subset_virtualChars (H : Subgroup ↥L) :
    indFam H (Irr ↥H) ⊆ (virtualChars ↥L : Set (↥L → ℂ)) := by
  intro f hf
  obtain ⟨W, hW⟩ := exists_fdRep_character_eq_of_mem_indFam H hf
  exact mem_virtualChars_of_mem_span_Irr (hW ▸ FDRep.character_mem_span_Irr W)

omit [Fintype G] in
theorem charSpanZero_le_dadeZDomain [H.Normal]
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hS : S ⊆ indFam H (Irr ↥H)) : charSpanZero S ≤ dadeZDomain L A := by
  intro f hf
  obtain ⟨hf1, hf2⟩ := mem_charSpanZero.1 hf
  have hmem : f ∈ dadeDomain L A := mem_dadeDomain_of_mem_span_indFam hA hS hf1 hf2
  refine mem_dadeZDomain.2 ⟨?_, fun x hx => dadeDomain.apply_eq_zero hmem hx⟩
  exact Submodule.span_le.2 (hS.trans (indFam_subset_virtualChars H)) hf1

omit [Fintype G] [Fintype ↥L] in
theorem charSpanZero_Irr_le_virtualChars (X : Type*) [Group X] :
    charSpanZero (Irr X) ≤ virtualChars X := by
  rw [virtualChars_eq_span_Irr]; exact charSpanZero_le _

noncomputable def dadeBaselineHom [H.Normal] (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hS : S ⊆ indFam H (Irr ↥H)) : charSpanZero S →+ virtualChars G :=
  ((Submodule.inclusion (charSpanZero_Irr_le_virtualChars G)).toAddMonoidHom.comp
    (dadeZMap hD)).comp
      (Submodule.inclusion (charSpanZero_le_dadeZDomain hA hS)).toAddMonoidHom

theorem coe_dadeBaselineHom [H.Normal] (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hS : S ⊆ indFam H (Irr ↥H)) (f : charSpanZero S) (F : dadeDomain L A)
    (hF : (F : ↥L → ℂ) = (f : ↥L → ℂ)) :
    ((dadeBaselineHom hD hA hS f : virtualChars G) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have h0 : ((dadeBaselineHom hD hA hS f : virtualChars G) : G → ℂ)
      = ((dadeZMap hD (Submodule.inclusion (charSpanZero_le_dadeZDomain hA hS) f) :
          charSpanZero (Irr G)) : G → ℂ) := rfl
  rw [h0, coe_dadeZMap]
  congr 2
  exact Subtype.ext hF.symm

noncomputable def nonprincipalBaselineHom [H.Normal] (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1})) :
    charSpanZero (indFam H (Irr ↥H \ {1})) →+ virtualChars G :=
  dadeBaselineHom hD hA (indFam_mono H Set.sdiff_subset)

theorem coe_nonprincipalBaselineHom [H.Normal] (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (f : charSpanZero (indFam H (Irr ↥H \ {1}))) (F : dadeDomain L A)
    (hF : (F : ↥L → ℂ) = (f : ↥L → ℂ)) :
    ((nonprincipalBaselineHom hD hA f : virtualChars G) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) :=
  coe_dadeBaselineHom hD hA _ f F hF

private theorem cfInner_zsmul_right' {α : Type*} [Fintype α] (d : ℤ) (f g : α → ℂ) :
    cfInner f (d • g) = (d : ℂ) * cfInner f g := by
  rw [← Int.cast_smul_eq_zsmul ℂ d g, cfInner_smul_right]; simp

omit [Fintype ↥L] in
theorem cfInner_eq_zero_of_mem_span_of_forall {ν : Submodule.span ℤ S →+ virtualChars G}
    (h : ∀ f, ∀ hf : f ∈ S, cfInner χ (ν ⟨f, Submodule.subset_span hf⟩ : G → ℂ) = 0)
    (g : Submodule.span ℤ S) : cfInner χ (ν g : G → ℂ) = 0 := by
  have key : ∀ (x : ↥L → ℂ) (hx : x ∈ Submodule.span ℤ S),
      cfInner χ (ν ⟨x, hx⟩ : G → ℂ) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero =>
      have h0 : (⟨(0 : ↥L → ℂ), Submodule.zero_mem _⟩ : Submodule.span ℤ S) = 0 := rfl
      rw [h0, map_zero]
      simpa using cfInner_zero_right χ
    | add u v hu hv ihu ihv =>
      have hadd : (⟨u + v, Submodule.add_mem _ hu hv⟩ : Submodule.span ℤ S)
          = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
      rw [hadd, map_add]
      have hc : ((ν ⟨u, hu⟩ + ν ⟨v, hv⟩ : virtualChars G) : G → ℂ)
          = (ν ⟨u, hu⟩ : G → ℂ) + (ν ⟨v, hv⟩ : G → ℂ) := by simp
      rw [hc, cfInner_add_right, ihu, ihv, add_zero]
    | smul d u hu ihu =>
      have hsm : (⟨d • u, Submodule.smul_mem _ d hu⟩ : Submodule.span ℤ S) = d • ⟨u, hu⟩ := rfl
      rw [hsm, map_zsmul]
      have hc : ((d • ν ⟨u, hu⟩ : virtualChars G) : G → ℂ) = d • (ν ⟨u, hu⟩ : G → ℂ) := by simp
      rw [hc, cfInner_zsmul_right', ihu, mul_zero]
  simpa using key (g : ↥L → ℂ) g.2

omit [Fintype G] in
theorem puncturedDiff_mem_charSpanZero [H.Normal]
    {ξ : ↥L → ℂ} (hζS : ζ ∈ indFam H (Irr ↥H \ {1}))
    (hξ : ξ ∈ indFam H (Irr ↥H \ {1})) (hζ1 : ζ 1 = (H.index : ℂ)) :
    puncturedDiff ζ ξ ∈ charSpanZero (indFam H (Irr ↥H \ {1})) := by
  obtain ⟨d, -, ⟨m, hm⟩, hd1⟩ :=
    exists_apply_one_eq_of_mem_indFam H (indFam_mono H Set.sdiff_subset hξ)
  have he : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  have hcoef : ξ 1 / ζ 1 = (m : ℂ) := by
    rw [hd1, hζ1, hm]; push_cast; field_simp
  have heq : puncturedDiff ζ ξ = ξ - (m : ℤ) • ζ := by
    rw [puncturedDiff_eq, hcoef, ← Int.cast_smul_eq_zsmul ℂ (m : ℤ) ζ]
    norm_num
  refine mem_charSpanZero.2 ⟨heq ▸ Submodule.sub_mem _ (Submodule.subset_span hξ)
    (Submodule.smul_mem _ _ (Submodule.subset_span hζS)), ?_⟩
  rw [puncturedDiff_apply, hcoef, hζ1, hd1, hm]
  push_cast; ring

theorem cfInner_dadeMap_puncturedDiff_eq_zero [H.Normal] (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    {ν : Submodule.span ℤ (indFam H (Irr ↥H \ {1})) →+ virtualChars G}
    (hν : IsCoherentWith (indFam H (Irr ↥H \ {1})) (nonprincipalBaselineHom hD hA) ν)
    (hperp : ∀ ξ, ∀ hξ : ξ ∈ indFam H (Irr ↥H \ {1}),
      cfInner χ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0)
    (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) (hζ1 : ζ 1 = (H.index : ℂ))
    {ξ : ↥L → ℂ} (hξ : ξ ∈ indFam H (Irr ↥H \ {1})) (F : dadeDomain L A)
    (hF : (F : ↥L → ℂ) = puncturedDiff ζ ξ) :
    cfInner ((dadeMap hD F : classFun G) : G → ℂ) χ = 0 := by
  set f : charSpanZero (indFam H (Irr ↥H \ {1})) :=
    ⟨puncturedDiff ζ ξ, puncturedDiff_mem_charSpanZero hζS hξ hζ1⟩ with hf
  rw [← coe_nonprincipalBaselineHom hD hA f F hF, ← hν.eq_on_zero f, ← conj_cfInner,
    cfInner_eq_zero_of_mem_span_of_forall hperp, map_zero]

omit [Fintype G] in
theorem eq_sdiff_map_of_eq_image
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1})) :
    A = ((H.map L.subtype : Subgroup G) : Set G) \ {1} := by
  subst hA
  ext x
  simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_map, Subgroup.coe_subtype]
  exact ⟨fun ⟨y, ⟨hyH, hy1⟩, hyx⟩ => hyx ▸ ⟨⟨y, hyH, rfl⟩, fun h => hy1 (by exact_mod_cast h)⟩,
    fun ⟨⟨y, hyH, hyx⟩, hx1⟩ => ⟨y, ⟨hyH, fun h => hx1 (by rw [← hyx, h]; rfl)⟩, hyx⟩⟩

omit [Fintype G] [Fintype ↥L] in
theorem indClassFun_one_apply_of_mem {M : Type*} [Group M] [Fintype M] (K : Subgroup M)
    [K.Normal] {y : M} (hy : y ∈ K) : indClassFun K (1 : ↥K → ℂ) y = (K.index : ℂ) := by
  classical
  have hall : ∀ t : M, t⁻¹ * y * t ∈ K := fun t => by
    simpa using ‹K.Normal›.conj_mem y hy t⁻¹
  have key : ∀ t : M,
      (if h : t⁻¹ * y * t ∈ K then (1 : ↥K → ℂ) ⟨t⁻¹ * y * t, h⟩ else 0) = 1 := fun t => by
    rw [dif_pos (hall t)]; rfl
  rw [indClassFun_apply, Finset.sum_congr rfl fun t _ => key t, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  have hK : (Nat.card ↥K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hcard : (K.index : ℂ) * (Nat.card ↥K : ℂ) = (Fintype.card M : ℂ) := by
    rw [← Nat.cast_mul, K.index_mul_card, Nat.card_eq_fintype_card]
  rw [← hcard, mul_comm (K.index : ℂ), ← mul_assoc, inv_mul_cancel₀ hK, one_mul]

omit [Fintype G] in
theorem puncturedDiff_indClassFun_one (hζ1 : ζ 1 = (H.index : ℂ)) :
    puncturedDiff ζ (indClassFun H (1 : ↥H → ℂ)) = indClassFun H (1 : ↥H → ℂ) - ζ := by
  have he : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  rw [puncturedDiff_eq, NormalInducedWeightedNorm.indClassFun_one_apply_one, hζ1, div_self he,
    one_smul]

omit [Fintype G] in
theorem cfInner_self_of_eq_const_on
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    {r : ↥L → ℂ} {c : ℂ} (hc : conj c = c)
    (hin : ∀ x : ↥L, x ∈ H → x ≠ 1 → r x = c)
    (hout : ∀ x : ↥L, (x : G) ∉ A → r x = 0) :
    cfInner r r = ((Nat.card ↥H : ℂ) - 1) / ((H.index : ℂ) * (Nat.card ↥H : ℂ)) * c ^ 2 := by
  classical
  have hmem : ∀ x : ↥L, (x : G) ∈ A ↔ x ∈ H ∧ x ≠ 1 := coe_mem_iff_mem_and_ne_one hA
  have hterm : ∀ x : ↥L, r x * conj (r x) = if x ∈ H ∧ x ≠ 1 then c * c else 0 := by
    intro x
    by_cases hx : x ∈ H ∧ x ≠ 1
    · rw [if_pos hx, hin x hx.1 hx.2, hc]
    · rw [if_neg hx, hout x (fun h => hx ((hmem x).1 h))]
      simp
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hcard : (Finset.univ.filter fun x : ↥L => x ∈ H ∧ x ≠ 1).card = Nat.card ↥H - 1 := by
    have hfe : (Finset.univ.filter fun x : ↥L => x ∈ H ∧ x ≠ 1)
        = (Finset.univ.filter fun x : ↥L => x ∈ H).erase 1 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      tauto
    have hHcard : (Finset.univ.filter fun x : ↥L => x ∈ H).card = Nat.card ↥H := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_coe
        (Finset.univ.filter fun x : ↥L => x ∈ H)]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp))
    rw [hfe, Finset.card_erase_of_mem (by simp), hHcard]
  rw [cfInner_def, Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_filter,
    Finset.sum_const, hcard]
  have hLH : (Nat.card ↥L : ℂ) = (H.index : ℂ) * (Nat.card ↥H : ℂ) := by
    rw [← Nat.cast_mul, H.index_mul_card]
  have h1 : ((Nat.card ↥H - 1 : ℕ) : ℂ) = (Nat.card ↥H : ℂ) - 1 := by
    rw [Nat.cast_sub hHpos]; norm_num
  rw [hLH, nsmul_eq_mul, h1]
  ring

section Main

variable [H.Normal] {ν : Submodule.span ℤ (indFam H (Irr ↥H \ {1})) →+ virtualChars G}

theorem conj_cfInner_dadeBeta (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) (hζ1 : ζ 1 = (H.index : ℂ)) (hχ : χ ∈ Irr G) :
    conj (cfInner (dadeBeta A R H ζ) χ) = cfInner (dadeBeta A R H ζ) χ := by
  obtain ⟨n, hn⟩ := exists_int_cfInner_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualChars (dadeBeta_mem_virtualChars hD hA hζS hζ1))
    (Submodule.subset_span hχ)
  rw [hn]
  simp

theorem dadeAverage_eq_cfInner_dadeBeta (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hν : IsCoherentWith (indFam H (Irr ↥H \ {1})) (nonprincipalBaselineHom hD hA) ν)
    (hχ : χ ∈ Irr G)
    (hperp : ∀ ξ, ∀ hξ : ξ ∈ indFam H (Irr ↥H \ {1}),
      cfInner χ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0)
    (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) (hζ1 : ζ 1 = (H.index : ℂ))
    {a : G} (ha : a ∈ A) :
    dadeAverage A R χ a = cfInner (dadeBeta A R H ζ) χ := by
  classical
  have : Fintype (indFam H (Irr ↥H)) := Fintype.ofFinite _
  have hA' : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1} := eq_sdiff_map_of_eq_image hA
  have he : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  set η : ↥L → ℂ := indClassFun H (1 : ↥H → ℂ) with hηdef
  set ηT : indFam H (Irr ↥H) := ⟨η, indClassFun_one_mem_indFam H⟩ with hηT
  set ζ₀ : indFam H (Irr ↥H) := ⟨ζ, indFam_mono H Set.sdiff_subset hζS⟩ with hζ₀
  have hζη : ζ₀ ≠ ηT := by
    intro h
    have h1 : ζ ∈ indFam H (Irr ↥H) \ {η} := by
      rw [hηdef, indFam_diff_singleton]; exact hζS
    exact h1.2 (by simpa [hζ₀, hηT] using congrArg (fun z : indFam H (Irr ↥H) => (z : ↥L → ℂ)) h)
  have haL : ((⟨a, hD.mem_of_mem ha⟩ : ↥L) : G) ∈ A := ha
  rw [dadeAverage_eq_sum_conj_cfInner_dadeMap_puncturedDiff hD hA'
    (Irr_subset_classFun hχ) ζ₀ haL]
  rw [Finset.sum_eq_single_of_mem ηT (Finset.mem_erase.2 ⟨Ne.symm hζη, Finset.mem_univ ηT⟩)]
  ·
    have hψ : (puncturedDiffDade hA' ζ₀ ηT : ↥L → ℂ) = η - ζ := by
      rw [coe_puncturedDiffDade]
      exact puncturedDiff_indClassFun_one hζ1
    have hβ : ((dadeMap hD (puncturedDiffDade hA' ζ₀ ηT) : classFun G) : G → ℂ)
        = dadeBeta A R H ζ := by
      rw [dadeBeta_eq_dadeMap hD (indClassFun_one_sub_mem_dadeDomain hA hζS hζ1)]
      congr 2
      exact Subtype.ext hψ
    have haH : (⟨a, hD.mem_of_mem ha⟩ : ↥L) ∈ H :=
      ((coe_mem_iff_mem_and_ne_one hA _).1 haL).1
    have hηa : (ηT : ↥L → ℂ) (⟨a, hD.mem_of_mem ha⟩ : ↥L) = (H.index : ℂ) :=
      indClassFun_one_apply_of_mem H haH
    have hnη : cfInner (ηT : ↥L → ℂ) (ηT : ↥L → ℂ) = (H.index : ℂ) :=
      NormalInducedWeightedNorm.cfInner_self_indClassFun_one H
    rw [hβ, hηa, hnη, mul_div_assoc, div_self he, mul_one,
      conj_cfInner_dadeBeta hD hA hζS hζ1 hχ]
  ·
    intro ξ hξ hξη
    have hξS : (ξ : ↥L → ℂ) ∈ indFam H (Irr ↥H \ {1}) := by
      rw [← indFam_diff_singleton]
      refine ⟨ξ.2, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro h
      exact hξη (Subtype.ext (by rw [h, hηT]))
    rw [cfInner_dadeMap_puncturedDiff_eq_zero hD hA hν hperp hζS hζ1 hξS _
      (coe_puncturedDiffDade hA' ζ₀ ξ), map_zero, zero_mul, zero_div]

theorem cfInner_self_dadeAverage (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hν : IsCoherentWith (indFam H (Irr ↥H \ {1})) (nonprincipalBaselineHom hD hA) ν)
    (hχ : χ ∈ Irr G)
    (hperp : ∀ ξ, ∀ hξ : ξ ∈ indFam H (Irr ↥H \ {1}),
      cfInner χ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0)
    (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) (hζ1 : ζ 1 = (H.index : ℂ)) :
    cfInner (fun y : ↥L => dadeAverage A R χ (y : G))
        (fun y : ↥L => dadeAverage A R χ (y : G))
      = ((Nat.card ↥H : ℂ) - 1) / ((H.index : ℂ) * (Nat.card ↥H : ℂ))
          * cfInner (dadeBeta A R H ζ) χ ^ 2 :=
  cfInner_self_of_eq_const_on hA (conj_cfInner_dadeBeta hD hA hζS hζ1 hχ)
    (fun x hxH hx1 => dadeAverage_eq_cfInner_dadeBeta hD hA hν hχ hperp hζS hζ1
      ((coe_mem_iff_mem_and_ne_one hA x).2 ⟨hxH, hx1⟩))
    fun _ hx => dadeAverage_eq_zero_of_notMem hx

theorem dadeAverage_spec (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hν : IsCoherentWith (indFam H (Irr ↥H \ {1})) (nonprincipalBaselineHom hD hA) ν)
    (hχ : χ ∈ Irr G)
    (hperp : ∀ ξ, ∀ hξ : ξ ∈ indFam H (Irr ↥H \ {1}),
      cfInner χ (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) = 0)
    (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) (hζ1 : ζ 1 = (H.index : ℂ)) :
    (∀ a ∈ A, dadeAverage A R χ a = cfInner (dadeBeta A R H ζ) χ) ∧
      cfInner (fun y : ↥L => dadeAverage A R χ (y : G))
          (fun y : ↥L => dadeAverage A R χ (y : G))
        = ((Nat.card ↥H : ℂ) - 1) / ((H.index : ℂ) * (Nat.card ↥H : ℂ))
            * cfInner (dadeBeta A R H ζ) χ ^ 2 :=
  ⟨fun _ ha => dadeAverage_eq_cfInner_dadeBeta hD hA hν hχ hperp hζS hζ1 ha,
    cfInner_self_dadeAverage hD hA hν hχ hperp hζS hζ1⟩

end Main

end NormalInducedFamily

end CFSG.FeitThompson
