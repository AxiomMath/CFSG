module

public import CFSG.FeitThompson.Representations.TypeIIIVLocalCharacterConstants
public import CFSG.FeitThompson.Representations.PrimeCubeDivisorInducedCoherence
public import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
public import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence
public import CFSG.FeitThompson.Representations.PrimeTIUniformNonprincipalConstants
public import CFSG.FeitThompson.Representations.CrossMaximalFirstWitnessValue
public import CFSG.FeitThompson.Local.PrimeCubeNonabelianCommutatorCentre
public import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep06

universe u

variable {G : Type*} [Group G] [Finite G] {M U W₁ W₂ : Subgroup G}

theorem IsWitnessedPConfiguration.hallCore_eq_commutator_of_bot
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) : hallCore ↥M = commutator ↥M := by
  refine Subgroup.map_injective M.subtype_injective ?_
  rw [Subgroup.map_subtype_commutator, ← hc.sup_hallCore_E, sup_bot_eq]

theorem IsWitnessedPConfiguration.derivedOf_eq_hallCore
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) : derivedOf M = hallCore ↥M :=
  (derivedOf_eq M).trans hc.hallCore_eq_commutator_of_bot.symm

theorem IsWitnessedPConfiguration.isNilpotent_derivedOf
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) : Group.IsNilpotent ↥(derivedOf M) := by
  rw [hc.derivedOf_eq_hallCore]
  infer_instance

theorem IsWitnessedPConfiguration.subgroupOf_W₂_le_commutator_derivedOf
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    W₂.subgroupOf M ≤ ⁅derivedOf M, derivedOf M⁆ := by
  have hmap : Subgroup.map M.subtype ⁅derivedOf M, derivedOf M⁆
      = ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ := by
    rw [Subgroup.map_commutator, map_subtype_derivedOf]
  have h2 := Subgroup.comap_mono (f := M.subtype) (hmap ▸ hc.le_commutator_commutator_W₂)
  rwa [Subgroup.comap_map_eq_self_of_injective M.subtype_injective] at h2

theorem IsWitnessedPConfiguration.fixesOnlyCommutatorCoset_subgroupOf
    [Group.IsSolvable ↥(derivedOf M)] (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    FrobeniusQuotientLayer.FixesOnlyCommutatorCoset (derivedOf M) (W₁.subgroupOf M) :=
  PrimeFixedTIPGroupCoherence.fixesOnlyCommutatorCoset_of_isPrimeCyclicTIHyp
    (hc.isPrimeCyclicTIHyp_subgroupOf hodd) hc.subgroupOf_W₂_le_commutator_derivedOf

theorem map_subtype_subgroupOf_of_le {H M : Subgroup G} (h : H ≤ M) :
    Subgroup.map M.subtype (H.subgroupOf M) = H := by
  rw [Subgroup.subgroupOf, Subgroup.map_comap_eq_self]
  simpa using h

theorem cyclicTIDiff_map_subgroupOf (h₁ : W₁ ≤ M) (h₂ : W₂ ≤ M) :
    cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
        (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))
      = cyclicTIset W₁ W₂ := by
  rw [Subgroup.map_sup, map_subtype_subgroupOf_of_le h₁, map_subtype_subgroupOf_of_le h₂]
  ext g
  rw [mem_cyclicTIDiff, mem_cyclicTIset]

theorem IsWitnessedPConfiguration.stabilizer_cyclicTIDiff_map
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) :
    {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
          (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))
      = cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
          (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))}
      = ((Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M) : Subgroup G) : Set G) := by
  rw [cyclicTIDiff_map_subgroupOf hc.le_M_W₁ hc.le_M_W₂, Subgroup.map_sup,
    map_subtype_subgroupOf_of_le hc.le_M_W₁, map_subtype_subgroupOf_of_le hc.le_M_W₂,
    setOf_conj_eq_self_eq_normalizer, hc.isTIWithNormalizer_cyclicTIset.normalizer_eq]

theorem IsWitnessedPConfiguration.inter_cyclicTIDiff_map_eq_empty
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂)
    {g : G} (hg : g ∉ Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M)) :
    (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
          (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))
      ∩ cyclicTIDiff (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
          (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M))
      = ∅ := by
  rw [Subgroup.map_sup, map_subtype_subgroupOf_of_le hc.le_M_W₁,
    map_subtype_subgroupOf_of_le hc.le_M_W₂] at hg
  rw [cyclicTIDiff_map_subgroupOf hc.le_M_W₁ hc.le_M_W₂, Set.inter_comm,
    ← Set.disjoint_iff_inter_eq_empty]
  exact hc.isTIWithNormalizer_cyclicTIset.disjoint_image_conj_inv hg

theorem IsWitnessedPConfiguration.isCyclicTIPair_map (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) :
    IsCyclicTIPair (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
      (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M)) :=
  (hc.isPrimeCyclicTIHyp_subgroupOf hodd).isCyclicTIPair_map_subtype
    hc.stabilizer_cyclicTIDiff_map fun _ hg => hc.inter_cyclicTIDiff_map_eq_empty hg

theorem IsWitnessedPConfiguration.exists_isCyclicTIIsometry_map [Fintype G]
    [Fintype ↥(Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))]
    (hodd : Odd (Nat.card G)) (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) :
    ∃ ω : ↥(classFun ↥(Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M)))
        →ₗ[ℂ] ↥(classFun G),
      IsCyclicTIIsometry (Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
        (Subgroup.map M.subtype (W₁.subgroupOf M)) (Subgroup.map M.subtype (W₂.subgroupOf M)) ω :=
  (hc.isCyclicTIPair_map hodd).exists_isCyclicTIIsometry

theorem IsWitnessedPConfiguration.image_bridgeSupport_subset_dadeA0
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) :
    (fun x : ↥M => (x : G)) ''
        bridgeSupport (((derivedOf M : Subgroup ↥M) : Set ↥M) \ {1})
          (W₁.subgroupOf M) (W₂.subgroupOf M)
      ⊆ dadeA0 M W₁ W₂ := by
  rw [Set.image_subset_iff]
  refine bridgeSupport_subset ?_ ?_
  · rintro x ⟨hxK, hx1⟩
    refine Set.mem_preimage.2 (sdiff_subset_dadeA0 M W₁ W₂ ⟨?_, fun hc1 => hx1 (Subtype.ext hc1)⟩)
    rw [← map_subtype_derivedOf M]
    exact ⟨x, hxK, rfl⟩
  · intro x hx
    obtain ⟨t, v, hv, hvt⟩ := mem_cyclicTIsetConj.1 hx
    refine Set.mem_preimage.2 (Or.inr ?_)
    rw [mixedConj_eq]
    refine Set.mem_iUnion₂.2 ⟨(t : G), t.2, (v : G), ?_, ?_⟩
    · obtain ⟨hv1, hv2, hv3⟩ := mem_cyclicTIset.1 hv
      refine mem_cyclicTIset.2 ⟨?_, hv2, hv3⟩
      have hmm : Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M) = W₁ ⊔ W₂ := by
        rw [Subgroup.map_sup, map_subtype_subgroupOf_of_le hc.le_M_W₁,
          map_subtype_subgroupOf_of_le hc.le_M_W₂]
      rw [← hmm]
      exact ⟨v, hv1, rfl⟩
    · rw [← hvt]; rfl

theorem IsWitnessedPConfiguration.stabilizer_punctured_eq_of_isTIWithNormalizer
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) (hTI : IsTIWithNormalizer (hallCoreSharp M) M) :
    {g : G | (fun x => g⁻¹ * x * g) ''
        (((Subgroup.map M.subtype (derivedOf M) : Subgroup G) : Set G) \ {1})
      = ((Subgroup.map M.subtype (derivedOf M) : Subgroup G) : Set G) \ {1}} = (M : Set G) := by
  have hsharp : hallCoreSharp M
      = ((Subgroup.map M.subtype (derivedOf M) : Subgroup G) : Set G) \ {1} := by
    rw [hallCoreSharp_eq, hc.derivedOf_eq_hallCore]
  rw [setOf_conj_eq_self_eq_normalizer, ← hsharp, hTI.normalizer_eq]

theorem IsWitnessedPConfiguration.inter_conj_punctured_eq_empty_of_isTIWithNormalizer
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂)
    (hTI : IsTIWithNormalizer (hallCoreSharp M) M) {g : G} (hg : g ∉ M) :
    (((Subgroup.map M.subtype (derivedOf M) : Subgroup G) : Set G) \ {1})
      ∩ ((fun x => g⁻¹ * x * g) ''
        (((Subgroup.map M.subtype (derivedOf M) : Subgroup G) : Set G) \ {1})) = ∅ := by
  have hsharp : hallCoreSharp M
      = ((Subgroup.map M.subtype (derivedOf M) : Subgroup G) : Set G) \ {1} := by
    rw [hallCoreSharp_eq, hc.derivedOf_eq_hallCore]
  rw [← hsharp, ← Set.disjoint_iff_inter_eq_empty]
  exact hTI.disjoint_image_conj_inv hg

section Family

variable [Fintype G]

open scoped Classical in
theorem indFamNonprincipal_eq_indFam_sdiff (M : Subgroup G) (K : Subgroup ↥M) :
    indFamNonprincipal M K = indFam K (Irr ↥K \ {1}) := by
  rw [indFamNonprincipal_eq, nonprincipalIrr_eq_sdiff_singleton]

open scoped Classical in
theorem indFamNonprincipal_eq_kerLayerIndFam (M : Subgroup G) (K : Subgroup ↥M) :
    indFamNonprincipal M K = NormalInducedFamily.kerLayerIndFam ⊥ K := by
  rw [indFamNonprincipal_eq_indFam_sdiff, CentralSectionCoherence.kerLayerIndFam_bot]

open scoped Classical in
theorem coe_fullFamily_eq_kerLayerIndFam (M : Subgroup G) (K : Subgroup ↥M) :
    (CentralSectionFullExtension.fullFamily K : Set (↥M → ℂ))
      = NormalInducedFamily.kerLayerIndFam ⊥ K := by
  rw [PrimeFixedTIPGroupCoherence.coe_fullFamily_eq_indFam_sdiff,
    CentralSectionCoherence.kerLayerIndFam_bot]

end Family

section Bridge

variable [Fintype G]

open scoped Classical in
theorem hasCoherentMap_of_isCoherent {S : Set (↥M → ℂ)}
    {τ : charSpanZero S →+ virtualChars G}
    (hτ : ∀ f : charSpanZero S, ((τ f : virtualChars G) : G → ℂ)
      = dadeMapFun M (dadeA0 M W₁ W₂) (dadeT M) (f : ↥M → ℂ))
    (h : IsCoherent S τ) : HasCoherentMap M W₁ W₂ S := by
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 h
  refine hasCoherentMap_iff.2 ⟨ν, hν.inner_eq, fun f hf1 => ?_⟩
  have hf : (f : ↥M → ℂ) ∈ charSpanZero S := mem_charSpanZero.2 ⟨f.2, hf1⟩
  have hkey := hν.eq_on_zero ⟨(f : ↥M → ℂ), hf⟩
  rw [show Submodule.inclusion (charSpanZero_le S) ⟨(f : ↥M → ℂ), hf⟩ = f from rfl] at hkey
  rw [hkey, hτ, dadeTau_eq]

open scoped Classical in
theorem hasCoherentMap_of_isCoherent_subTauHom {R : (↥M → ℂ) → Finset (G → ℂ)}
    (hsub : IsSubcoherent (CentralSectionFullExtension.fullFamily (derivedOf M))
      (dadeMapFun M (dadeA0 M W₁ W₂) (dadeT M)) R)
    {U : Set (↥M → ℂ)}
    (hUS : U ⊆ (CentralSectionFullExtension.fullFamily (derivedOf M) : Set (↥M → ℂ)))
    (h : IsCoherent U (WeightedFeitExtension.subTauHom hsub hUS)) :
    HasCoherentMap M W₁ W₂ U := by
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 h
  refine hasCoherentMap_iff.2 ⟨ν, hν.inner_eq, fun f hf1 => ?_⟩
  have hf : (f : ↥M → ℂ) ∈ charSpanZero U := mem_charSpanZero.2 ⟨f.2, hf1⟩
  have hkey := hν.eq_on_zero ⟨(f : ↥M → ℂ), hf⟩
  rw [show Submodule.inclusion (charSpanZero_le U) ⟨(f : ↥M → ℂ), hf⟩ = f from rfl] at hkey
  rw [hkey, WeightedFeitExtension.subTauHom_apply, dadeTau_eq]

open scoped Classical in
theorem coe_subDadeHom_eq_dadeMapFun [(derivedOf M).Normal] {P : Set (↥M → ℂ)}
    (hD : IsDadeData M (dadeA0 M W₁ W₂) (dadeT M))
    (hPS : P ⊆ indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1}))
    (hA₀ : (fun x : ↥M => (x : G)) ''
      bridgeSupport (((derivedOf M : Subgroup ↥M) : Set ↥M) \ {1})
        (W₁.subgroupOf M) (W₂.subgroupOf M) ⊆ dadeA0 M W₁ W₂)
    (f : charSpanZero P) :
    ((TypeVTwoFamilyJoining.subDadeHom (W₁ := W₁.subgroupOf M) (W₂ := W₂.subgroupOf M)
        hD hPS hA₀ f : virtualChars G) : G → ℂ)
      = dadeMapFun M (dadeA0 M W₁ W₂) (dadeT M) (f : ↥M → ℂ) := by
  have hmem : (f : ↥M → ℂ) ∈ dadeDomain M (dadeA0 M W₁ W₂) :=
    mem_dadeDomain_of_mem_dadeZDomain
      (TypeVTwoFamilyJoining.charSpanZero_le_dadeZDomain hPS hA₀ f.2)
  rw [TypeVTwoFamilyJoining.coe_subDadeHom hD hPS hA₀ f ⟨(f : ↥M → ℂ), hmem⟩ rfl, coe_dadeMap]

end Bridge

section Packages

variable [Fintype G]

open scoped Classical in
theorem IsWitnessedPConfiguration.exists_pivot (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) :
    ∃ ζ : ↥M → ℂ, ζ ∈ indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1}) ∧ ζ ∈ Irr ↥M ∧
      ζ 1 = (Nat.card ↥(W₁.subgroupOf M) : ℂ) := by
  classical
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hKn := h.normal
  have hnt : Nontrivial ↥(derivedOf M) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 fun hbot =>
      h.right_ne_bot (le_bot_iff.1 (hbot ▸ h.right_le))
  have hsolv : Group.IsSolvable ↥(derivedOf M) := by
    have := hc.isNilpotent_derivedOf
    infer_instance
  obtain ⟨lam, hlam, hne, -, hind, hdeg⟩ :=
    exists_mem_Irr_indClassFun_mem_Irr_of_centralizer_le_commutator
      (K := derivedOf M) (E := W₁.subgroupOf M) h.isComplement'_left.symm h.coprime_natCard
      fun e he he1 => by
        rw [h.centralizer_eq e he he1]
        exact hc.subgroupOf_W₂_le_commutator_derivedOf
  exact ⟨indClassFun (derivedOf M) lam, (mem_indFam _).2 ⟨lam, ⟨hlam, hne⟩, rfl⟩, hind, hdeg⟩

open scoped Classical in
theorem IsWitnessedPConfiguration.exists_isSubcoherent_fullFamily (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂)
    (hD : IsDadeData M (dadeA0 M W₁ W₂) (dadeT M)) :
    ∃ R : (↥M → ℂ) → Finset (G → ℂ),
      IsSubcoherent (CentralSectionFullExtension.fullFamily (derivedOf M))
        (dadeMapFun M (dadeA0 M W₁ W₂) (dadeT M)) R := by
  classical
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hKn := h.normal
  have := Fintype.ofFinite ↑(Irr ↥(W₁.subgroupOf M))
  have := Fintype.ofFinite ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)
  have := Fintype.ofFinite ↥(Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
  obtain ⟨σ, hσ⟩ := h.exists_isCyclicTIIsometry
  obtain ⟨ω, hω⟩ := hc.exists_isCyclicTIIsometry_map hodd
  obtain ⟨R, hR, -⟩ := PrimeDadeSubcoherence.exists_isSubcoherent_indFamDetect
    (ω := ω) (A₀ := dadeA0 M W₁ W₂) (T := dadeT M) hodd h hσ
    (H := derivedOf M) h.right_le le_rfl
    (A := ((derivedOf M : Subgroup ↥M) : Set ↥M) \ {1})
    (fun t => PrimeFixedTIPGroupCoherence.conj_image_punctured_eq (derivedOf M) t)
    (fun y _ _ => PrimeFixedTIPGroupCoherence.centralizer_sdiff_subset_punctured (derivedOf M) y)
    hc.image_bridgeSupport_subset_dadeA0 hD hc.stabilizer_cyclicTIDiff_map
    (fun _ hg => hc.inter_cyclicTIDiff_map_eq_empty hg) hω
    (PrimeFixedTIPGroupCoherence.coe_fullFamily_eq_indFamDetect_self (derivedOf M))
  exact ⟨R, hR⟩

end Packages

section Chief

variable [Fintype G]

open scoped Classical in
theorem IsWitnessedPConfiguration.obstruction_of_not_hasCoherentMap (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂)
    (hD : IsDadeData M (dadeA0 M W₁ W₂) (dadeT M))
    (hnc : ¬ HasCoherentMap M W₁ W₂ (indFamNonprincipal M (derivedOf M))) :
    (⁅derivedOf M, derivedOf M⁆ : Subgroup ↥M).relIndex (derivedOf M)
        ≤ 4 * Nat.card ↥(W₁.subgroupOf M) ^ 2 + 1 ∧
      ¬ IsMulCommutative ↥(derivedOf M) ∧
      ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ Nat.card ↥(derivedOf M) = p ^ a ∧
        ¬ Nat.card ↥(W₁.subgroupOf M) ∣ p - 1 := by
  classical
  obtain ⟨R, hsub⟩ := hc.exists_isSubcoherent_fullFamily hodd hD
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hKn := h.normal
  have hnil : Group.IsNilpotent ↥(derivedOf M) := hc.isNilpotent_derivedOf
  have hModd : Odd (Nat.card ↥M) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hK : derivedOf M ≠ ⊥ := fun hbot => h.right_ne_bot (le_bot_iff.1 (hbot ▸ h.right_le))
  have hnc' : ¬ IsCoherent (NormalInducedFamily.kerLayerIndFam (⊥ : Subgroup ↥M) (derivedOf M))
      (WeightedFeitExtension.subTauHom hsub
        (CentralSectionCoherence.kerLayerIndFam_subset_of_eq_bot
          (coe_fullFamily_eq_kerLayerIndFam M (derivedOf M)) ⊥)) := fun hcoh =>
    hnc (indFamNonprincipal_eq_kerLayerIndFam M (derivedOf M) ▸
      hasCoherentMap_of_isCoherent_subTauHom hsub _ hcoh)
  obtain ⟨-, hbd, hnab, p, a, -, hp, ha, -, hcard, -, hdvd⟩ :=
    QuotientFrobeniusNoncoherent.obstruction_of_not_isCoherent (E := W₁.subgroupOf M)
      hsub hModd hK (coe_fullFamily_eq_kerLayerIndFam M (derivedOf M)) h.mul_eq_univ h.inf_eq_bot
      (hc.fixesOnlyCommutatorCoset_subgroupOf hodd) hnc'
  exact ⟨hbd, hnab, p, a, hp, ha, hcard, hdvd⟩

end Chief

section AlternativeOne

variable [Fintype G]

open scoped Classical in
theorem IsWitnessedPConfiguration.hasCoherentMap_of_isTIWithNormalizer (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂)
    (hD : IsDadeData M (dadeA0 M W₁ W₂) (dadeT M))
    (hTI : IsTIWithNormalizer (hallCoreSharp M) M)
    {p a : ℕ} (hp : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a)
    (hcard : Nat.card ↥(derivedOf M) = p ^ a)
    (hnab : ¬ IsMulCommutative ↥(derivedOf M))
    (hW₂ : Nat.card ↥(W₂.subgroupOf M) = p) :
    HasCoherentMap M W₁ W₂ (indFamNonprincipal M (derivedOf M)) := by
  classical
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hKn := h.normal
  have := Fintype.ofFinite ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)
  have := Fintype.ofFinite ↥(Subgroup.map M.subtype (W₁.subgroupOf M ⊔ W₂.subgroupOf M))
  have := Fintype.ofFinite ↑(Irr ↥(W₁.subgroupOf M))
  obtain ⟨σ, hσ⟩ := h.exists_isCyclicTIIsometry
  obtain ⟨ω, hω⟩ := hc.exists_isCyclicTIIsometry_map hodd
  obtain ⟨ζ, hζmem, hζirr, hζ1⟩ := hc.exists_pivot hodd
  have hdata : PrimeFixedTIPGroupCoherence.IsPrimeFixedTIPGroupData p a (derivedOf M)
      (W₁.subgroupOf M) (W₂.subgroupOf M) σ ω (dadeA0 M W₁ W₂) (dadeT M) ζ :=
    { primeCyclicTI := h
      sigma_isometry := hσ
      odd_natCard := hodd
      isDadeData := hD
      image_subset := hc.image_bridgeSupport_subset_dadeA0
      stabilizer_cyclicTIDiff_eq := hc.stabilizer_cyclicTIDiff_map
      inter_cyclicTIDiff_eq_empty := fun _ hg => hc.inter_cyclicTIDiff_map_eq_empty hg
      omega_isometry := hω
      zeta_mem := hζmem
      zeta_irr := hζirr
      zeta_apply_one := hζ1
      prime := hp
      odd_prime := hpodd
      one_le_exponent := ha
      not_isMulCommutative := hnab
      natCard_eq_pow := hcard
      natCard_right_eq_prime := hW₂
      right_le_commutator := hc.subgroupOf_W₂_le_commutator_derivedOf
      stabilizer_punctured_eq := hc.stabilizer_punctured_eq_of_isTIWithNormalizer hTI
      inter_conj_punctured_eq_empty := fun _ hg =>
        hc.inter_conj_punctured_eq_empty_of_isTIWithNormalizer hTI hg }
  rw [indFamNonprincipal_eq_indFam_sdiff]
  refine hasCoherentMap_of_isCoherent
    (τ := TypeVTwoFamilyJoining.subDadeHom (W₁ := W₁.subgroupOf M) (W₂ := W₂.subgroupOf M)
      hD (subset_refl _) hc.image_bridgeSupport_subset_dadeA0)
    (coe_subDadeHom_eq_dadeMapFun hD _ _) ?_
  exact PrimeFixedTIPGroupCoherence.isCoherent_indFam_sdiff hdata _
    (coe_subDadeHom_eq_dadeMapFun hD _ _)

end AlternativeOne

section AlternativeThree

variable [Fintype G]

theorem relIndex_commutator_eq_sq_of_card_eq_prime_cube {L : Type*} [Group L] {K : Subgroup L}
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card ↥K = p ^ 3) (hnab : ¬ IsMulCommutative ↥K) :
    (⁅K, K⁆ : Subgroup L).relIndex K = p ^ 2 := by
  have hcomm : Nat.card ↥(commutator ↥K) = p :=
    card_commutator_of_card_eq_prime_cube hp hcard hnab
  have hmul := Subgroup.card_mul_index (commutator ↥K)
  rw [hcomm, hcard] at hmul
  rw [relIndex_commutator_self_eq_index_commutator]
  have h3 : p ^ 3 = p * p ^ 2 := by ring
  rw [h3] at hmul
  exact Nat.eq_of_mul_eq_mul_left hp.pos hmul

open scoped Classical in
theorem IsWitnessedPConfiguration.hasCoherentMap_of_prime_cube (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂)
    (hD : IsDadeData M (dadeA0 M W₁ W₂) (dadeT M))
    (hW₂p : (Nat.card ↥W₂).Prime) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥(derivedOf M) = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥(derivedOf M))
    (hsq : p ^ 2 ≤ 4 * Nat.card ↥(W₁.subgroupOf M) ^ 2 + 1)
    (hdvd : Nat.card ↥(W₁.subgroupOf M) ∣ p + 1) :
    HasCoherentMap M W₁ W₂ (indFamNonprincipal M (derivedOf M)) := by
  classical
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hKn := h.normal
  have hModd : Odd (Nat.card ↥M) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hcard2 : Nat.card ↥(W₂.subgroupOf M) = Nat.card ↥W₂ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₂
  have hp2 : (Nat.card ↥(W₂.subgroupOf M)).Prime := by rw [hcard2]; exact hW₂p
  have hW₂card : Nat.card ↥(W₂.subgroupOf M) = p :=
    (Nat.prime_dvd_prime_iff_eq hp2 hp).1
      (hp2.dvd_of_dvd_pow (n := 3) (hcard ▸ Subgroup.card_dvd_of_le h.right_le))
  have hKodd : Odd (Nat.card ↥(derivedOf M)) :=
    hModd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hpodd : Odd p := by
    rw [hcard] at hKodd
    exact (Nat.odd_pow_iff (by norm_num)).1 hKodd
  have hW₂le : W₂.subgroupOf M ≤ commutator ↥M := derivedOf_eq M ▸ h.right_le
  obtain ⟨σ, hσ⟩ := h.exists_isCyclicTIIsometry
  obtain ⟨ω, hω⟩ := hc.exists_isCyclicTIIsometry_map hodd
  obtain ⟨ζ, hζmem, hζirr, hζ1⟩ := hc.exists_pivot hodd
  obtain ⟨d, hdodd, hd1, s, hspm, n, hneven, hn2, hdn, hall⟩ :=
    h.exists_primeTIirr_constants hσ hModd hp2 hW₂le
  have hdt : ((d.toNat : ℤ)) = d := Int.toNat_of_nonneg (by omega)
  have hnt : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg (by omega)
  have hC : PrimeCubeDivisorCoherence.IsPrimeCubeDivisorHyp h σ ζ p d.toNat n.toNat s
      (dadeA0 M W₁ W₂) (dadeT M) ω :=
    { arrayHyp :=
      { isometry := hσ
        zeta_mem_indFam := hζmem
        zeta_mem_Irr := hζirr
        zeta_one := hζ1
        one_lt_d := by omega
        two_le_n := by omega
        sign := by rcases hspm with h1 | h1 <;> rw [h1] <;> norm_num
        primeTIirr_one_eq := fun i j hj => by rw [(hall i j hj).1]; exact_mod_cast hdt.symm
        primeTISign_eq := fun j hj => (hall (principalIrr _) j hj).2.2
        degree_eq := by
          have hz : (d.toNat : ℤ) - s = (n.toNat : ℤ) * (Nat.card ↥(W₁.subgroupOf M) : ℤ) := by
            rw [hdt, hnt, hdn]
          exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hz
        prime := hp
        odd := hpodd
        card_K := hcard
        not_isMulCommutative := hnab
        card_W₂ := hW₂card
        le_commutator := hc.subgroupOf_W₂_le_commutator_derivedOf }
      sq_le := hsq
      dvd := hdvd
      odd := hodd
      isDadeData := hD
      image_subset := hc.image_bridgeSupport_subset_dadeA0
      stabilizer_eq := hc.stabilizer_cyclicTIDiff_map
      inter_eq_empty := fun _ hg => hc.inter_cyclicTIDiff_map_eq_empty hg
      omega_isometry := hω }
  rw [indFamNonprincipal_eq_indFam_sdiff]
  exact hasCoherentMap_of_isCoherent (coe_subDadeHom_eq_dadeMapFun hD _ hC.image_subset)
    hC.exists_isCoherent_indFam

end AlternativeThree

theorem hasCoherentMap_of_isTypeV
    (_h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (_h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Fintype G] (_hG : IsMinimalOddSimple G)
    {M W₁ W₂ : Subgroup G} (_hM : IsCoatom M) (_htype : IsTypeV M)
    (_hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) :
    HasCoherentMap M W₁ W₂ (indFamNonprincipal M (derivedOf M)) := by
  classical
  have hD : IsDadeData M (dadeA0 M W₁ W₂) (dadeT M) :=
    (_h₁ G _hG M ⊥ W₁ W₂ _hM (Or.inr (Or.inr _htype)) _hc).2.2.2.1
  have hW₂p : (Nat.card ↥W₂).Prime := _h₃ G _hG M ⊥ W₁ W₂ _hM (Or.inr (Or.inr _htype)) _hc
  have hodd := _hG.odd
  have hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ :=
    natCard_subgroupOf_eq_of_le _hc.le_M_W₁
  by_contra hnc
  obtain ⟨hbd, hnab, p, a, hp, ha, hcard, hdvd⟩ :=
    _hc.obstruction_of_not_hasCoherentMap hodd hD hnc
  have hrp : ∀ r ∈ (Nat.card ↥(hallCore ↥M)).primeFactors, r = p := fun r hr => by
    rw [← _hc.derivedOf_eq_hallCore, hcard, Nat.primeFactors_prime_pow (by omega) hp] at hr
    simpa using hr
  obtain ⟨-, h1 | ⟨r, hr, -, hrdvd⟩ | ⟨r, hr, -, hcube, hrdvd⟩⟩ :=
    _htype.clauses_of_isWitnessedPConfiguration_of_minimalSimple _hG.simple _hG.nonabelian
      _hG.odd _hG.solvable _hM _hc
  ·
    have hpodd : Odd p := by
      have hKodd : Odd (Nat.card ↥(derivedOf M)) :=
        (hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)).of_dvd_nat
          (Subgroup.card_subgroup_dvd_card _)
      rw [hcard] at hKodd
      exact (Nat.odd_pow_iff (by omega)).1 hKodd
    have hW₂card : Nat.card ↥(W₂.subgroupOf M) = p := by
      have hp2 : (Nat.card ↥(W₂.subgroupOf M)).Prime := by
        rw [natCard_subgroupOf_eq_of_le _hc.le_M_W₂]; exact hW₂p
      exact (Nat.prime_dvd_prime_iff_eq hp2 hp).1
        (hp2.dvd_of_dvd_pow (n := a)
          (hcard ▸ Subgroup.card_dvd_of_le (_hc.isPrimeCyclicTIHyp_subgroupOf hodd).right_le))
    exact hnc (_hc.hasCoherentMap_of_isTIWithNormalizer hodd hD h1 hp hpodd ha hcard hnab hW₂card)
  ·
    exact hdvd (hcard1 ▸ hrp r hr ▸ hrdvd)
  ·
    have hrp' : r = p := hrp r hr
    subst hrp'
    have hcube' : Nat.card ↥(derivedOf M) = r ^ 3 := by
      have htop : pCore r ↥(derivedOf M) = ⊤ :=
        pCore_eq_top_of_isPGroup hp (IsPGroup.of_card hcard)
      rw [_hc.derivedOf_eq_hallCore.symm, htop] at hcube
      rwa [← Subgroup.card_top (G := ↥(derivedOf M))]
    have hsq : r ^ 2 ≤ 4 * Nat.card ↥(W₁.subgroupOf M) ^ 2 + 1 := by
      rwa [relIndex_commutator_eq_sq_of_card_eq_prime_cube hp hcube' hnab] at hbd
    exact hnc (_hc.hasCoherentMap_of_prime_cube hodd hD hW₂p hp hcube' hnab hsq
      (hcard1 ▸ hrdvd))

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson CFSG.FeitThompson.Prep06

universe u

theorem FPF_type_v_exclusion
    (h₁ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₂ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₃ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_v_exclusion.{u} := by
  intro G _ _ hG M hM htype
  obtain ⟨W₁, W₂, hc, -⟩ := htype.exists_isWitnessedPConfiguration
  exact h₂ G hG M ⊥ W₁ W₂ hM (Or.inr (Or.inr htype)) hc
    (hasCoherentMap_of_isTypeV h₁ h₃ hG hM htype hc)

end CFSG.FeitThompson.Proofs

end
