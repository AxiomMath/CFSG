module

public import CFSG.FeitThompson.Representations.TypeIIIVExtendedDadeSupport
public import CFSG.FeitThompson.Representations.TypeIIIVLocalCharacterConstants
public import CFSG.FeitThompson.Representations.CoherentLocalRowImagesColumnSum
public import CFSG.FeitThompson.Representations.CoherentInducedImageVanishesMixedTI
public import CFSG.FeitThompson.Representations.DisjointDadeSupportsOrthogonalIrreducibles
import CFSG.FeitThompson.Representations.TypeVMaximalExclusion
import CFSG.FeitThompson.OddOrder.TypeIIIVCoreAbelianizationBound
import all CFSG.FeitThompson.Representations.UniformLocalBridgePuncturedSupportNorm
import all CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CrossedRowData

open Subgroup Pointwise CFSG.FeitThompson.Prep06

variable {G : Type*} [Group G] {M U W₁ W₂ : Subgroup G}

theorem map_subtype_subgroupOf_sup (h₁ : W₁ ≤ M) (h₂ : W₂ ≤ M) :
    (W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype = W₁ ⊔ W₂ := by
  rw [← Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_subgroupOf_eq_of_le (sup_le h₁ h₂)]

theorem cyclicTIDiff_map_subtype_eq (h₁ : W₁ ≤ M) (h₂ : W₂ ≤ M) :
    cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
        ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype)
      = cyclicTIset W₁ W₂ := by
  rw [map_subtype_subgroupOf_sup h₁ h₂, Subgroup.map_subgroupOf_eq_of_le h₁,
    Subgroup.map_subgroupOf_eq_of_le h₂]
  ext x
  rw [mem_cyclicTIDiff, mem_cyclicTIset]

theorem setOf_conj_eq_of_isWitnessedPConfiguration [Finite G]
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
          ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype)
      = cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
          ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype)}
      = (((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype : Subgroup G) : Set G) := by
  rw [cyclicTIDiff_map_subtype_eq hc.le_M_W₁ hc.le_M_W₂, setOf_conj_eq_self_eq_normalizer,
    hc.normalizer_cyclicTIset, map_subtype_subgroupOf_sup hc.le_M_W₁ hc.le_M_W₂]

theorem inter_eq_empty_of_isWitnessedPConfiguration [Finite G]
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ∀ g ∉ (W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
            ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype)
        ∩ cyclicTIDiff ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
            ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype) = ∅ := by
  intro g hg
  rw [map_subtype_subgroupOf_sup hc.le_M_W₁ hc.le_M_W₂] at hg
  rw [cyclicTIDiff_map_subtype_eq hc.le_M_W₁ hc.le_M_W₂, Set.inter_comm]
  exact Set.disjoint_iff_inter_eq_empty.1
    (hc.isTIWithNormalizer_cyclicTIset.disjoint_image_conj_inv hg)

theorem isCyclicTIPair_map_subtype [Finite G] (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsCyclicTIPair ((W₁.subgroupOf M ⊔ W₂.subgroupOf M).map M.subtype)
      ((W₁.subgroupOf M).map M.subtype) ((W₂.subgroupOf M).map M.subtype) :=
  (hc.isPrimeCyclicTIHyp_subgroupOf hodd).isCyclicTIPair_map_subtype
    (setOf_conj_eq_of_isWitnessedPConfiguration hc)
    (inter_eq_empty_of_isWitnessedPConfiguration hc)

theorem isCyclicTIPair_sup [Finite G] (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M U W₁ W₂) : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := by
  have h := isCyclicTIPair_map_subtype hodd hc
  rwa [map_subtype_subgroupOf_sup hc.le_M_W₁ hc.le_M_W₂,
    Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₁,
    Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₂] at h

theorem w_eq_basisProdIrr [Fintype G] (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G}
    {w : ↑(Irr ↥W₁) → ↑(Irr ↥W₂) → classFun ↥(W₁ ⊔ W₂)}
    {η : ↑(Irr ↥W₁) → ↑(Irr ↥W₂) → G → ℂ} (hη : IsEtaSetup W₁ W₂ ω w η)
    (i : Irr ↥W₁) (j : Irr ↥W₂) : w i j = hW.basisProdIrr (i, j) := by
  refine Subtype.ext (funext fun z => ?_)
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ W₁, ∃ y ∈ W₂, x * y = (z : G) := by
    have hz : (z : G) ∈ (W₁ : Set G) * (W₂ : Set G) := by rw [hW.mul_eq]; exact z.2
    obtain ⟨x, hx, y, hy, hxy⟩ := hz
    exact ⟨x, hx, y, hy, hxy⟩
  rw [hW.coe_basisProdIrr_apply]
  have hzeq : z = (⟨x * y, hxy ▸ z.2⟩ : ↥(W₁ ⊔ W₂)) := Subtype.ext hxy.symm
  rw [hzeq, hη.prod i j ⟨x, hx⟩ ⟨y, hy⟩ _ rfl, hW.prodChar_apply_mul _ _ hx hy]

theorem eta_eq_prodCharEta [Fintype G] (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G}
    {w : ↑(Irr ↥W₁) → ↑(Irr ↥W₂) → classFun ↥(W₁ ⊔ W₂)}
    {η : ↑(Irr ↥W₁) → ↑(Irr ↥W₂) → G → ℂ} (hη : IsEtaSetup W₁ W₂ ω w η)
    (i : Irr ↥W₁) (j : Irr ↥W₂) : η i j = hW.prodCharEta ω i j := by
  rw [hη.eta_eq i j, w_eq_basisProdIrr hW hη i j, IsCyclicTIPair.prodCharEta_eq_coe_apply]

theorem image_sdiff_derivedOf (M : Subgroup G) :
    (fun x : ↥M => (x : G)) '' ((derivedOf M : Set ↥M) \ {1})
      = ((⁅M, M⁆ : Subgroup G) : Set G) \ {1} := by
  have hmapK : Subgroup.map M.subtype (derivedOf M) = (⁅M, M⁆ : Subgroup G) :=
    map_subtype_derivedOf M
  have h : ((fun x : ↥M => (x : G))) = M.subtype := rfl
  rw [h, Set.image_sdiff M.subtype_injective,
    show (M.subtype '' (derivedOf M : Set ↥M)) = ((⁅M, M⁆ : Subgroup G) : Set G) from by
      rw [← hmapK]; rfl]
  simp

theorem dadeDeltaM_eq_totalDadeSupport [Finite G] (M : Subgroup G) :
    dadeDeltaM M
      = totalDadeSupport ((fun x : ↥M => (x : G)) '' ((derivedOf M : Set ↥M) \ {1}))
          (dadeT M) := by
  rw [dadeDeltaM_eq, image_sdiff_derivedOf]

theorem image_primeTIbridgeSupport_subset_dadeA0 [Finite G]
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    (fun x : ↥M => (x : G)) ''
        primeTIbridgeSupport (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      ⊆ dadeA0 M W₁ W₂ := by
  have hmapK : Subgroup.map M.subtype (derivedOf M) = (⁅M, M⁆ : Subgroup G) :=
    map_subtype_derivedOf M
  have hsup : Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M) = W₁ ⊔ W₂ :=
    map_subtype_subgroupOf_sup hc.le_M_W₁ hc.le_M_W₂
  have hcTI : ∀ a : ↥M, a ∈ cyclicTIset (W₁.subgroupOf M) (W₂.subgroupOf M) →
      (a : G) ∈ cyclicTIset W₁ W₂ := by
    intro a ha
    obtain ⟨hmem, hn1, hn2⟩ := mem_cyclicTIset.1 ha
    exact mem_cyclicTIset.2 ⟨by rw [← hsup]; exact ⟨a, hmem, rfl⟩, hn1, hn2⟩
  rintro g ⟨x, hx, rfl⟩
  rw [dadeA0_eq]
  rw [show primeTIbridgeSupport (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      = ((derivedOf M : Set ↥M) \ {1})
        ∪ Group.conjugatesOfSet (cyclicTIset (W₁.subgroupOf M) (W₂.subgroupOf M)) from rfl] at hx
  rcases hx with hx1 | hx1
  · refine Or.inl ⟨?_, ?_⟩
    · rw [← hmapK]; exact ⟨x, hx1.1, rfl⟩
    · simp only [Set.mem_singleton_iff]
      intro hh
      exact hx1.2 (by simp [Subtype.ext_iff, hh])
  · right
    rw [Group.mem_conjugatesOfSet_iff] at hx1
    obtain ⟨a, ha, hconj⟩ := hx1
    obtain ⟨m, hm⟩ := isConj_iff.1 hconj
    refine CFSG.FeitThompson.Proofs.mem_mixedConj.2
      ⟨((m : G))⁻¹, M.inv_mem m.2, (a : G), hcTI a ha, ?_⟩
    have hx2 : ((m * a * m⁻¹ : ↥M) : G) = (x : G) := by rw [hm]
    push_cast at hx2
    simpa using hx2

set_option maxHeartbeats 1000000 in
open scoped Classical in
theorem exists_uniformBridgeData [Fintype G] (hG : IsMinimalOddSimple G)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hprime : (Nat.card W₂).Prime)
    (hD : IsDadeData M (dadeA0 M W₁ W₂) (dadeT M))
    (hcoh : HasCoherentMap M W₁ W₂ (Prep06.indFamNonprincipal M (derivedOf M)))
    (h : IsPrimeCyclicTIHyp (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M)) :
    ∃ (σ : classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) →ₗ[ℂ] classFun ↥M) (ζ : ↥M → ℂ)
        (d n δ : ℤ) (ν : Submodule.span ℤ
          (indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1})) →+ virtualChars G),
      1 < d ∧ (δ = 1 ∨ δ = -1) ∧ h.IsUniformBridgeData σ ζ d n δ ∧
        (∀ f g : Submodule.span ℤ (indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1})),
          cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : ↥M → ℂ) (g : ↥M → ℂ)) ∧
        ∀ (f : Submodule.span ℤ (indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1})))
          (F : dadeDomain M (dadeA0 M W₁ W₂)), (f : ↥M → ℂ) = (F : ↥M → ℂ) →
            (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
  classical
  have hfin : Finite G := Finite.of_fintype G
  have hnK : (derivedOf M).Normal := h.normal
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hsolvM : Group.IsSolvable ↥M := hG.solvable M hc.lt_top.ne
  have hsolvK : Group.IsSolvable ↥(derivedOf M) := by
    have hh : derivedOf M = commutator ↥M := rfl
    rw [hh]; infer_instance
  have hcard2 : Nat.card ↥(W₂.subgroupOf M) = Nat.card ↥W₂ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₂
  have hp : (Nat.card ↥(W₂.subgroupOf M)).Prime := by rw [hcard2]; exact hprime
  have hW₂le : W₂.subgroupOf M ≤ commutator ↥M := derivedOf_eq M ▸ h.right_le
  obtain ⟨σ, hσ⟩ := h.exists_isCyclicTIIsometry
  obtain ⟨d, hdodd, hd1, δ, hδ, n, hneven, hn2, hsubeq, hall⟩ :=
    h.exists_primeTIirr_constants hσ hModd hp hW₂le
  have hmapK : Subgroup.map M.subtype (derivedOf M) = (⁅M, M⁆ : Subgroup G) :=
    map_subtype_derivedOf M
  have hKbot : derivedOf M ≠ ⊥ := by
    intro hh
    have h2 := hc.ne_bot_commutator
    rw [← hmapK, hh] at h2
    simp at h2
  have hfix : FrobeniusQuotientLayer.FixesOnlyCommutatorCoset (derivedOf M) (W₁.subgroupOf M) :=
    hc.fixesOnlyCommutatorCoset_subgroupOf hG.odd
  obtain ⟨ζ, hζmem⟩ := FrobeniusQuotientLayer.kerLayerIndFam_commutator_nonempty
    (K := derivedOf M) (L := ↥M) hKbot
  have hζIrr : ζ ∈ Irr ↥M :=
    FrobeniusQuotientLayer.kerLayerIndFam_commutator_subset_Irr h.mul_eq_univ hfix hζmem
  have hζ1 : ζ 1 = (Nat.card ↥(W₁.subgroupOf M) : ℂ) :=
    FrobeniusQuotientLayer.apply_one_eq_card_of_mem_kerLayerIndFam_commutator
      h.mul_eq_univ h.inf_eq_bot hζmem
  have hζfam : ζ ∈ indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1}) := by
    obtain ⟨θ, hθ, hθe⟩ := NormalInducedFamily.mem_kerLayerIndFam.1 hζmem
    obtain ⟨hθ1, -, hθ3⟩ := NormalInducedFamily.mem_kerLayerIrr.1 hθ
    exact hθe ▸ Set.mem_image_of_mem (indClassFun (derivedOf M))
      (show θ ∈ Irr ↥(derivedOf M) \ {1} from ⟨hθ1, hθ3⟩)
  have hlocal : h.IsUniformBridgeData σ ζ d n δ :=
    ⟨hσ, hζfam, hζIrr, hζ1, hd1, hn2, hδ, fun i j hj => (hall i j hj).1,
      fun j hj => (hall (principalIrr ↥(W₁.subgroupOf M)) j hj).2.2, hsubeq⟩
  have hfameq : Prep06.indFamNonprincipal M (derivedOf M)
      = indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1}) := by
    rw [indFamNonprincipal_eq, nonprincipalIrr_eq_sdiff_singleton]
  rw [hfameq] at hcoh
  obtain ⟨ν, hνinner, hνtau⟩ := hcoh
  refine ⟨σ, ζ, d, n, δ, ν, hd1, hδ, hlocal, hνinner, fun f F hfF => ?_⟩
  have hF1 : (F : ↥M → ℂ) 1 = 0 := by
    refine (mem_dadeDomain.1 F.2).2 1 ?_
    intro hh
    have h5 := hD.subset_sdiff hh
    simp at h5
  have hf1 : (f : ↥M → ℂ) 1 = 0 := by rw [hfF]; exact hF1
  rw [hνtau f hf1, coe_dadeMap hD F, ← hfF, dadeTau_eq]

variable {L : Subgroup G} {K X₁ X₂ : Subgroup ↥L}

theorem coe_nu_apply_eq_zero_of_mem_charSpanZero [Fintype G] [Fintype ↥L] [K.Normal]
    [Fintype ↥(X₁ ⊔ X₂)] [Fintype ↥((X₁ ⊔ X₂).map L.subtype)]
    {σ : classFun ↥(X₁ ⊔ X₂) →ₗ[ℂ] classFun ↥L} {ζ : ↥L → ℂ} {d n δ : ℤ}
    {A : Set G} {T : G → Subgroup G}
    {ω : classFun ↥((X₁ ⊔ X₂).map L.subtype) →ₗ[ℂ] classFun G}
    {ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G}
    {h : IsPrimeCyclicTIHyp K X₁ X₂}
    (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν)
    {f : ↥L → ℂ} (hf : f ∈ charSpanZero (indFam K (Irr ↥K \ {1})))
    {z : G} (hz : z ∉ totalDadeSupport ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) T) :
    (ν ⟨f, charSpanZero_le _ hf⟩ : G → ℂ) z = 0 := by
  have hDp := isDadeData_puncturedCore hC.isDadeData hC.image_puncturedCore_subset
  have hdom : f ∈ dadeDomain L ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) :=
    NormalInducedFamily.mem_dadeDomain_of_mem_span_indFam (H := K) rfl
      (indFam_mono K Set.sdiff_subset) (charSpanZero_le _ hf) (charSpanZero_apply_one ⟨f, hf⟩)
  have heq : (ν ⟨f, charSpanZero_le _ hf⟩ : G → ℂ)
      = ((dadeMap hDp ⟨f, hdom⟩ : classFun G) : G → ℂ) :=
    coe_nu_eq_dadeMap_puncturedCore hC.isDadeData hC.image_puncturedCore_subset hC.nu_eq_tau _
      ⟨f, hdom⟩ rfl
  rw [heq]
  by_contra hne
  exact hz (support_dadeMap_subset hDp ⟨f, hdom⟩ hne)

set_option maxHeartbeats 800000 in
theorem exists_row_witness_of_isUniformBridgeData [Fintype G] [Fintype ↥L] [K.Normal]
    [Fintype ↥(X₁ ⊔ X₂)] [Fintype ↑(Irr ↥X₁)] [Fintype ↥((X₁ ⊔ X₂).map L.subtype)]
    {σ : classFun ↥(X₁ ⊔ X₂) →ₗ[ℂ] classFun ↥L} {ζ : ↥L → ℂ} {d n δ : ℤ}
    {A : Set G} {T : G → Subgroup G}
    {ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G}
    {h : IsPrimeCyclicTIHyp K X₁ X₂}
    {Wamb V₁ V₂ : Subgroup G} [Fintype ↥Wamb] [Fintype ↑(Irr ↥V₁)]
    {ωa : classFun ↥Wamb →ₗ[ℂ] classFun G}
    (hmapW : (X₁ ⊔ X₂).map L.subtype = Wamb) (hmap1 : X₁.map L.subtype = V₁)
    (hmap2 : X₂.map L.subtype = V₂)
    (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hodd : Odd (Nat.card G)) (hD : IsDadeData L A T)
    (himg : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K X₁ X₂ ⊆ A)
    (hWpair : IsCyclicTIPair Wamb V₁ V₂) (hωa : IsCyclicTIIsometry Wamb V₁ V₂ ωa)
    (hνinner : ∀ f g : Submodule.span ℤ (indFam K (Irr ↥K \ {1})),
      cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ))
    (hντ : ∀ (f : Submodule.span ℤ (indFam K (Irr ↥K \ {1}))) (F : dadeDomain L A),
      (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ)) :
    ∃ ρ : G → ℂ, ρ ∈ signedIrr G ∧ star ρ ≠ ρ ∧
      (∀ (p : Irr ↥V₁) (q : Irr ↥V₂), cfInner ρ (hWpair.prodCharEta ωa p q) = 0) ∧
      (∀ z ∉ totalDadeSupport ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) T,
        (ρ - star ρ) z = 0) ∧
      ∀ q : Irr ↥V₂, q ≠ principalIrr ↥V₂ →
        ∀ z ∉ totalDadeSupport ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) T,
          ((δ : ℂ) • (∑ p : Irr ↥V₁, hWpair.prodCharEta ωa p q) - (d : ℂ) • ρ) z = 0 := by
  subst hmapW hmap1 hmap2
  have hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ωa ν :=
    ⟨hB, hodd, hD, himg, hWpair, hωa, hνinner, hντ⟩
  have hW2K : X₂.map L.subtype ≤ K.map L.subtype := Subgroup.map_mono h.right_le
  have hW1K : X₁.map L.subtype ⊓ K.map L.subtype = ⊥ := by
    rw [← Subgroup.map_inf_eq X₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]
  refine ⟨hC.nuZeta, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC.nuZeta_def]
    exact ExtendedDade.nu_mem_signedIrr hC.odd hC.isDadeData hC.image_puncturedCore_subset rfl
      hC.nu_inner hC.nu_eq_tau hC.local_data.mem_indFam hC.local_data.mem_Irr
  · rw [hC.nuZeta_def]
    exact ExtendedDade.star_nu_ne hC.odd hC.isDadeData hC.image_puncturedCore_subset rfl
      hC.nu_inner hC.nu_eq_tau hC.local_data.mem_indFam hC.local_data.mem_Irr
  · intro p q
    rw [hC.nuZeta_def]
    exact ExtendedDade.cfInner_nu_prodCharEta_eq_zero hC.odd hC.isDadeData
      hC.image_puncturedCore_subset hC.cyclicTIDiff_subset_param rfl hC.nu_inner hC.nu_eq_tau
      hC.local_data.mem_indFam hC.local_data.mem_Irr hWpair
      (Subgroup.map_subtype_le _) hW2K hW1K hωa p q
  · intro z hz
    have hsub := NormalInducedFamily.support_coe_nu_sub_star_subset (H := K)
      hC.odd (isDadeData_puncturedCore hC.isDadeData hC.image_puncturedCore_subset)
      rfl rfl hC.nu_inner
      (coe_nu_eq_dadeMap_puncturedCore hC.isDadeData hC.image_puncturedCore_subset hC.nu_eq_tau)
      hC.local_data.mem_indFam hC.local_data.mem_Irr
    have hns : z ∉ Function.support
        ((ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ : G → ℂ)
          - star (ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ : G → ℂ)) :=
      fun hmem => hz (hsub hmem)
    rw [hC.nuZeta_def]
    simpa [Function.mem_support] using hns
  · intro q hq z hz
    obtain ⟨k, hk⟩ := irrMapSubtype_surjective L X₂ q
    have hk0 : k ≠ principalIrr ↥X₂ := by
      intro hcon
      rw [hcon, irrMapSubtype_principal] at hk
      exact hq hk.symm
    have hsum : (∑ p : Irr ↥(X₁.map L.subtype), hWpair.prodCharEta ωa p q)
        = ∑ i : Irr ↥X₁, hC.etaLocal i k := by
      refine (Fintype.sum_bijective (irrMapSubtype L X₁) (irrMapSubtype_bijective L X₁)
        _ _ ?_).symm
      intro i
      rw [hC.etaLocal_def, hk]
    rw [hsum]
    have hf := primeTIrow_sub_smul_zeta_mem_charSpanZero hC.local_data hk0
    have hkey := hC.nuRow_sub_smul_nuZeta hk0
    rw [hC.nuRow_eq_smul_sum_etaLocal hk0] at hkey
    rw [hkey]
    exact coe_nu_apply_eq_zero_of_mem_charSpanZero hC hf hz

set_option maxHeartbeats 1000000 in
open scoped Classical in
theorem exists_crossed_row_data [Fintype G] (_hG : IsMinimalOddSimple G)
    (_hM : IsCoatom M) (_hc : IsWitnessedPConfiguration M U W₁ W₂)
    (_hprime : (Nat.card W₂).Prime)
    (_hD : IsDadeData M (dadeA0 M W₁ W₂) (dadeT M))
    (_hcoh : HasCoherentMap M W₁ W₂ (Prep06.indFamNonprincipal M (derivedOf M)))
    {ω : ↥(classFun ↥(W₁ ⊔ W₂)) →ₗ[ℂ] ↥(classFun G)}
    {w : ↑(Irr ↥W₁) → ↑(Irr ↥W₂) → ↥(classFun ↥(W₁ ⊔ W₂))}
    {η : ↑(Irr ↥W₁) → ↑(Irr ↥W₂) → G → ℂ} (_hη : IsEtaSetup W₁ W₂ ω w η) :
    ∃ d : ℕ, ∃ δ : ℂ, ∃ ρ : G → ℂ,
      1 < d ∧ (δ = 1 ∨ δ = -1) ∧ ρ ∈ signedIrr G ∧ star ρ ≠ ρ ∧
        (∀ i j, cfInner ρ (η i j) = 0) ∧
        SupportedOn (dadeDeltaM M) (ρ - star ρ) ∧
        ∀ j : ↑(Irr ↥W₂), j ≠ principalIrr ↥W₂ →
          SupportedOn (dadeDeltaM M) (δ • (∑ᶠ i : ↑(Irr ↥W₁), η i j) - (d : ℂ) • ρ) := by
  classical
  have hfin : Finite G := Finite.of_fintype G
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  have hloc : IsPrimeCyclicTIHyp (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M) :=
    _hc.isPrimeCyclicTIHyp_subgroupOf _hG.odd
  have : (derivedOf M).Normal := hloc.normal
  have hWpair : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := isCyclicTIPair_sup _hG.odd _hc
  obtain ⟨σ, ζ, d, n, δ, ν, hd1, hδ, hB, hνinner, hντ⟩ :=
    exists_uniformBridgeData _hG _hc _hprime _hD _hcoh hloc
  obtain ⟨ρ, hρIrr, hρnr, hρorth, hρsupp, hρrow⟩ :=
    exists_row_witness_of_isUniformBridgeData
      (map_subtype_subgroupOf_sup _hc.le_M_W₁ _hc.le_M_W₂)
      (Subgroup.map_subgroupOf_eq_of_le _hc.le_M_W₁)
      (Subgroup.map_subgroupOf_eq_of_le _hc.le_M_W₂)
      hB _hG.odd _hD (image_primeTIbridgeSupport_subset_dadeA0 _hc) hWpair _hη.isometry
      hνinner hντ
  have hηeq : ∀ i j, η i j = hWpair.prodCharEta ω i j := eta_eq_prodCharEta hWpair _hη
  have hdnn : ((d.toNat : ℤ)) = d := Int.toNat_of_nonneg (by omega)
  have hdC : ((d.toNat : ℕ) : ℂ) = ((d : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hdnn
  refine ⟨d.toNat, (δ : ℂ), ρ, by omega, ?_, hρIrr, hρnr, ?_, ?_, ?_⟩
  · rcases hδ with hh | hh
    · left; rw [hh]; norm_num
    · right; rw [hh]; norm_num
  · intro i j
    rw [hηeq i j]
    exact hρorth i j
  · intro g hg
    rw [dadeDeltaM_eq_totalDadeSupport] at hg
    exact hρsupp g hg
  · intro j hj g hg
    rw [dadeDeltaM_eq_totalDadeSupport] at hg
    have hsum : (∑ᶠ i : ↑(Irr ↥W₁), η i j) = ∑ i : ↑(Irr ↥W₁), hWpair.prodCharEta ω i j := by
      rw [finsum_eq_sum_of_fintype]
      exact Finset.sum_congr rfl fun i _ => hηeq i j
    rw [hsum, hdC]
    exact hρrow j hj g hg

end CrossedRowData

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson CFSG.FeitThompson.CrossedRowData
open CFSG.FeitThompson.Prep06

universe u

open scoped Classical in
theorem FPF_type_iii_v_coherent_crossed_row_data
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₃ : Statements.FPF_type_iii_v_second_factor_prime.{u})
    (h₄ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₅ : Statements.FTS_canonical_signalizer_structure.{u}) :
    Statements.FPF_type_iii_v_coherent_crossed_row_data.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc hcoh ω w η hη
  have hD : IsDadeData M (dadeA0 M W₁ W₂) (dadeT M) :=
    isDadeData_dadeA0 h₁ h₂ h₄ h₅ hG hM htype hc
  have hprime : (Nat.card W₂).Prime := h₃ G hG M U W₁ W₂ hM htype hc
  exact exists_crossed_row_data hG hM hc hprime hD hcoh hη

end CFSG.FeitThompson.Proofs

end
