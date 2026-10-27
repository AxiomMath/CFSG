module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Representations.PrimeTILocalBridgeSupportNorm
import CFSG.FeitThompson.Representations.CoreDetectingFamilyAntirealBlocks
import CFSG.FeitThompson.Representations.QuotientLayerDegreeSquareSum
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.TypeIIIVLocalCharacterConstants
import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep06

theorem irrDetect_top_eq_nonprincipalIrr (K : Type*) [Group K] [Finite K] :
    irrDetect ℂ (⊤ : Subgroup K) = nonprincipalIrr K := by
  ext θ
  rw [mem_irrDetect_iff_values, mem_nonprincipalIrr, Irr_eq_irrChar]
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · obtain ⟨x, -, hx⟩ := h.2
    intro hcon
    exact hx (by rw [hcon]; rfl)
  · by_contra hcon
    simp only [not_exists, not_and] at hcon
    exact h.2 (eq_one_of_mem_Irr_of_forall_apply_eq ((Irr_eq_irrChar K).symm ▸ h.1)
      fun k => by simpa using hcon k (mem_top k))

theorem indFamDetect_top_eq_indFam_nonprincipalIrr {L : Type*} [Group L] [Fintype L]
    (K : Subgroup L) : indFamDetect K (⊤ : Subgroup ↥K) = indFam K (nonprincipalIrr ↥K) := by
  rw [indFamDetect_eq_indFam, irrDetect_top_eq_nonprincipalIrr]

variable {G : Type*} [Group G] [Finite G] {M W₁ W₂ U : Subgroup G}

theorem map_subtype_sup_subgroupOf (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M) = W₁ ⊔ W₂ := by
  rw [← Subgroup.subgroupOf_sup hc.le_M_W₁ hc.le_M_W₂,
    Subgroup.map_subgroupOf_eq_of_le (sup_le hc.le_M_W₁ hc.le_M_W₂)]

theorem cyclicTIDiff_map_subtype_eq (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
      (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))
      = cyclicTIset W₁ W₂ := by
  rw [map_subtype_sup_subgroupOf hc, Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₁,
    Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₂, cyclicTIDiff_sup_eq_cyclicTIset]

theorem setOf_conj_cyclicTIDiff_map_subtype (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
          (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))
      = cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
          (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))}
      = ((Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M) : Subgroup G) : Set G) := by
  rw [cyclicTIDiff_map_subtype_eq hc, map_subtype_sup_subgroupOf hc,
    setOf_conj_eq_self_eq_normalizer, hc.isTIWithNormalizer_cyclicTIset.normalizer_eq]

theorem inter_conj_cyclicTIDiff_map_subtype (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ∀ g ∉ Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M),
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
            (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))
        ∩ cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
            (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))
        = ∅ := by
  intro g hg
  rw [map_subtype_sup_subgroupOf hc] at hg
  rw [cyclicTIDiff_map_subtype_eq hc, Set.inter_comm]
  exact Set.disjoint_iff_inter_eq_empty.1
    (hc.isTIWithNormalizer_cyclicTIset.disjoint_image_conj_inv hg)

theorem coe_mem_cyclicTIset_of_mem (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {v : ↥M} (hv : v ∈ cyclicTIset (W₁.subgroupOf M) (W₂.subgroupOf M)) :
    (v : G) ∈ cyclicTIset W₁ W₂ := by
  rw [mem_cyclicTIset] at hv ⊢
  refine ⟨?_, fun hcon => hv.2.1 (Subgroup.mem_subgroupOf.2 hcon),
    fun hcon => hv.2.2 (Subgroup.mem_subgroupOf.2 hcon)⟩
  rw [← map_subtype_sup_subgroupOf hc]
  exact ⟨v, hv.1, rfl⟩

theorem image_cyclicTIsetConj_subset_mixedConj (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    (fun x : ↥M => (x : G)) ''
        cyclicTIsetConj (W₁.subgroupOf M) (W₂.subgroupOf M) ⊆ mixedConj M W₁ W₂ := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨t, v, hv, rfl⟩ := mem_cyclicTIsetConj.1 hx
  exact Set.mem_biUnion (t : ↥M).2 ⟨(v : G), coe_mem_cyclicTIset_of_mem hc hv, by push_cast; rfl⟩

omit [Finite G] in
theorem coe_mem_sdiff_commutator {M : Subgroup G} {x : ↥M}
    (hx : x ∈ (derivedOf M : Subgroup ↥M)) (hx1 : x ≠ 1) :
    (x : G) ∈ ((⁅M, M⁆ : Subgroup G) : Set G) \ {1} :=
  ⟨by rw [← map_subtype_derivedOf M]; exact ⟨x, hx, rfl⟩, fun hcon => hx1 (Subtype.ext hcon)⟩

theorem image_bridgeSupport_sdiff_subset_dadeA0 (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    (fun x : ↥M => (x : G)) ''
        bridgeSupport (((derivedOf M : Subgroup ↥M) : Set ↥M) \ {1})
          (W₁.subgroupOf M) (W₂.subgroupOf M) ⊆ dadeA0 M W₁ W₂ := by
  rw [image_bridgeSupport]
  refine Set.union_subset ?_
    ((image_cyclicTIsetConj_subset_mixedConj hc).trans Set.subset_union_right)
  rintro _ ⟨x, ⟨hx, hx1⟩, rfl⟩
  exact Set.subset_union_left (coe_mem_sdiff_commutator hx hx1)

omit [Finite G] in
theorem conj_image_sdiff_derivedOf_eq (M : Subgroup G) (t : ↥M) :
    (fun a => t⁻¹ * a * t) '' (((derivedOf M : Subgroup ↥M) : Set ↥M) \ {1})
      = ((derivedOf M : Subgroup ↥M) : Set ↥M) \ {1} := by
  have hKn : (derivedOf M : Subgroup ↥M).Normal := by rw [derivedOf_eq]; infer_instance
  ext x
  simp only [Set.mem_image, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  refine ⟨?_, fun hx => ⟨t * x * t⁻¹, ⟨?_, ?_⟩, by group⟩⟩
  · rintro ⟨y, ⟨hy, hy1⟩, rfl⟩
    refine ⟨by simpa using hKn.conj_mem y hy t⁻¹, fun hcon => hy1 ?_⟩
    have hy' : y = t * (t⁻¹ * y * t) * t⁻¹ := by group
    rw [hy', hcon]; group
  · simpa using hKn.conj_mem x hx.1 t
  · refine fun hcon => hx.2 ?_
    have hx' : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [hx', hcon]; group

omit [Finite G] in
theorem sdiff_inf_centralizer_subset (M : Subgroup G) {y : ↥M} :
    (((derivedOf M : Subgroup ↥M) ⊓ Subgroup.centralizer {y} : Subgroup ↥M) : Set ↥M) \ {1}
      ⊆ ((derivedOf M : Subgroup ↥M) : Set ↥M) \ {1} :=
  fun _ hz => ⟨(Subgroup.mem_inf.1 hz.1).1, hz.2⟩

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson CFSG.FeitThompson.Prep06

universe u

open scoped Classical in
theorem FPF_type_iii_iv_weighted_normal_family
    (h₁ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₂ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u}) :
    Statements.FPF_type_iii_iv_weighted_normal_family.{u} := by
  classical
  intro G _ _ hG M U W₁ W₂ hM htype hc S hS
  have htype' : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M := htype.imp_right Or.inl
  obtain ⟨-, -, -, hD, htau⟩ := h₁ G hG M U W₁ W₂ hM htype' hc
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hG.odd
  have hKn : (derivedOf M).Normal := h.normal
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  have hSdet : S = indFamDetect (derivedOf M) ((derivedOf M).subgroupOf (derivedOf M)) := by
    rw [hS, indFamNonprincipal_eq, Subgroup.subgroupOf_self,
      indFamDetect_top_eq_indFam_nonprincipalIrr]
  have hStop : S = indFamDetect (derivedOf M) (⊤ : Subgroup ↥(derivedOf M)) := by
    rwa [Subgroup.subgroupOf_self] at hSdet
  have hAconj := conj_image_sdiff_derivedOf_eq M
  have hA : ∀ y ∈ (derivedOf M : Subgroup ↥M), y ≠ 1 →
      (((derivedOf M) ⊓ Subgroup.centralizer {y} : Subgroup ↥M) : Set ↥M) \ {1}
        ⊆ ((derivedOf M : Subgroup ↥M) : Set ↥M) \ {1} :=
    fun y _ _ => sdiff_inf_centralizer_subset M
  have hA₀ := image_bridgeSupport_sdiff_subset_dadeA0 hc
  have hvanish : ∀ f ∈ Submodule.span ℤ S, f 1 = 0 →
      ∀ x : ↥M, (x : G) ∉ dadeA0 M W₁ W₂ → f x = 0 := by
    intro f hf hf1 x hx
    refine PrimeDadeSubcoherence.apply_eq_zero_of_mem_intSpanZeroAtOne
      (H := derivedOf M) hAconj hA (mem_intSpanZeroAtOne.2 ⟨by rwa [← hSdet], hf1⟩) ?_
    exact fun hmem => hx (sdiff_subset_dadeA0 M W₁ W₂ (coe_mem_sdiff_commutator hmem.1
      (fun hc1 => hmem.2 hc1)))
  have hspanIrr : ∀ f ∈ Submodule.span ℤ S, f ∈ Submodule.span ℤ (Irr ↥M) := fun f hf =>
    Submodule.span_le.2
      (fun g hg => PrimeDadeSubcoherence.mem_span_Irr_of_mem_indFamDetect (hStop ▸ hg)) hf
  obtain ⟨σ, hσ⟩ := h.exists_isCyclicTIIsometry
  obtain ⟨ω, hω⟩ := (h.isCyclicTIPair_map_subtype (setOf_conj_cyclicTIDiff_map_subtype hc)
    (inter_conj_cyclicTIDiff_map_subtype hc)).exists_isCyclicTIIsometry
  obtain ⟨R, hsub, -, -, -⟩ := PrimeDadeSubcoherence.exists_isSubcoherent_indFamDetect
    (L := M) (K := derivedOf M) (W₁ := W₁.subgroupOf M) (W₂ := W₂.subgroupOf M)
    (σ := σ) (ω := ω) (A₀ := dadeA0 M W₁ W₂) (T := dadeT M) hG.odd h hσ
    (H := derivedOf M) h.right_le le_rfl hAconj hA hA₀ hD
    (setOf_conj_cyclicTIDiff_map_subtype hc) (inter_conj_cyclicTIDiff_map_subtype hc) hω
    (S := indFamDetectFinset (derivedOf M) ((derivedOf M).subgroupOf (derivedOf M)))
    (by rw [coe_indFamDetectFinset])
  have hmemF : ∀ f ∈ S,
      f ∈ indFamDetectFinset (derivedOf M) ((derivedOf M).subgroupOf (derivedOf M)) :=
    fun f hf => mem_indFamDetectFinset.2 (hSdet ▸ hf)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact fun f hf => ⟨PrimeDadeSubcoherence.ne_zero_of_mem_indFamDetect (hStop ▸ hf),
      PrimeDadeSubcoherence.isCharacter_of_mem_indFamDetect (hStop ▸ hf)⟩
  ·
    exact fun f hf => hStop ▸ PrimeDadeSubcoherence.star_mem_indFamDetect (hStop ▸ hf)
  ·
    exact fun f hf =>
      PrimeDadeSubcoherence.star_ne_self_of_mem_indFamDetect_of_odd_natCard hG.odd (hStop ▸ hf)
  ·
    exact fun f hf g hg hne =>
      PrimeDadeSubcoherence.cfInner_eq_zero_of_mem_indFamDetect (hStop ▸ hf) (hStop ▸ hg) hne
  ·
    intro f hf g hg hf1 hg1
    obtain ⟨hadd, -, hinner, hZ, -⟩ := htau f g
      (mem_classFun_of_mem_span_Irr (hspanIrr f hf))
      (mem_classFun_of_mem_span_Irr (hspanIrr g hg)) (hvanish f hf hf1) (hvanish g hg hg1)
    refine ⟨hadd, hinner, ?_, hZ (by rw [virtualChars_eq_span_Irr]; exact hspanIrr f hf)⟩
    exact PrimeDadeSubcoherence.dadeMapFun_apply_one_eq_zero hD
      (mem_dadeDomain.2 ⟨mem_classFun_of_mem_span_Irr (hspanIrr f hf), hvanish f hf hf1⟩)
  ·
    refine ⟨fun f => ((R f : Finset (G → ℂ)) : Set (G → ℂ)),
      fun f hf => ⟨(R f).finite_toSet, ?_, ?_, ?_⟩, ?_⟩
    · intro r hr
      rw [SetLike.mem_coe, virtualChars_eq_span_Irr]
      exact virtualCharSpan_le_span_Irr G (hsub.R_subset f (hmemF f hf) r hr)
    · intro r hr s hs
      rw [← charInner_eq_cfInner]
      by_cases hrs : r = s
      · subst hrs; simpa using hsub.charInner_R_self f (hmemF f hf) r hr
      · simpa [hrs] using hsub.charInner_R_of_ne f (hmemF f hf) r hr s hs hrs
    · rw [dadeTau_eq, hsub.tau_sub_star f (hmemF f hf), finsum_mem_coe_finset]
    · intro f hf g hg hgf hgsf r hr s hs
      rw [← charInner_eq_cfInner]
      exact hsub.charInner_R_R f (hmemF f hf) g (hmemF g hg) hgf hgsf r hr s hs
  ·
    exact hS ▸ h₂ G hG M U W₁ W₂ hM htype' hc

end CFSG.FeitThompson.Proofs
