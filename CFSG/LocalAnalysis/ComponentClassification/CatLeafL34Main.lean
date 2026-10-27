module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Hull
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup
open scoped commutatorElement

variable {M : Type} [Group M] [Finite M]

theorem le_pLayer_of_isPComponent_centralizer {a : M} (ha : orderOf a = 2) {J : Subgroup M}
    (hJa : J ≤ centralizer ({a} : Set M))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set M)))) : J ≤ pLayer M 2 := by
  have h1 : J.subgroupOf (centralizer ({a} : Set M)) ≤
      pLayer ↥(centralizer ({a} : Set M)) 2 := le_sSup hJ
  have h2 := map_mono (f := (centralizer ({a} : Set M)).subtype) h1
  rw [map_subgroupOf_eq_of_le hJa] at h2
  have hza : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ha, pow_one])
  have h3 := ClassicalInvolution.l2PrimeBalance M (zpowers a) hza
  rw [UnbalancedLayer.centralizer_zpowers_eq] at h3
  exact h2.trans h3

theorem map_pPrimeCore_le_of_isPComponent {K : Subgroup M} (hK : IsPComponent 2 K) :
    (pPrimeCore 2 K).map K.subtype ≤ pPrimeCore 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 K hK.choose_spec.2.1,
    subgroupOf_map_subtype]
  exact inf_le_left

theorem nonempty_pPrimeCore_quotient_equiv_held (hHe : TBLit.HeldTrivialMultiplier)
    {K : Subgroup M} (hK : IsPComponent 2 K)
    (eH : (K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K) ≃* Blueprint.NativeSporadic.He) :
    Nonempty (K ⧸ pPrimeCore 2 K ≃* Blueprint.NativeSporadic.He) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := hHe (K ⧸ pPrimeCore 2 K)
    (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 K hK) ⟨eH⟩
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans
    eH⟩

theorem nonempty_held_of_strict (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hHe : TBLit.HeldTrivialMultiplier) (hKM : SectionRank.IsKGroupCat M) {a x : M}
    {J K : Subgroup M} (hT : UnbalancedLayer.GSUnbalancingTriple a x J)
    (hJL : GrSLit.IsL34Type (J ⧸ Open.fusionZStar J)) (hK : IsPComponent 2 K)
    (hKa : conjugate K a = K) (hJK : J ≤ K)
    (hJp : IsPComponent 2 (J.subgroupOf (K ⊓ centralizer ({a} : Set M))))
    (hlt : (pPrimeCore 2 J).index < (pPrimeCore 2 K).index) :
    Nonempty (K ⧸ pPrimeCore 2 K ≃* Blueprint.NativeSporadic.He) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ha, hx, -, hJa, hJ, hJx, hJD⟩ := UnbalancedLayer.gsUnbalancingTriple_iff.mp hT
  obtain ⟨σ, P, hPF, ⟨eP⟩⟩ :=
    exists_properFixedComponent_of_stable ha hK hKa (le_inf hJK hJa) hJp hlt
  have hP34 : GrSLit.IsL34Type (P ⧸ Open.fusionZStar P) :=
    LieType.CurtisTits.lieModel_of_mulEquiv eP hJL
  obtain ⟨s, hs, hs2⟩ := exists_involution_of_isL34Type hJL
  have hJperf : ⁅J, J⁆ = J := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hJ
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hJa).toMonoidHom) (subgroupOfEquivOfLe hJa).surjective)
  have hxK : x ∈ normalizer (K : Set M) := mem_normalizer_of_le_pComponent hK hJK hJperf hs hs2
    (UnbalancingLocal.le_normalizer_of_commutator_le hJx.le (mem_zpowers x))
  set O := (pPrimeCore 2 (centralizer ({x} : Set M))).map (centralizer ({x} : Set M)).subtype
    with hOdef
  set D := O ⊓ normalizer (K : Set M) with hDdef
  have hD₀D : O ⊓ centralizer ({a} : Set M) ≤ D := le_inf inf_le_left fun d hd =>
    mem_normalizer_of_le_pComponent hK hJK hJperf hs hs2
      (UnbalancingLocal.le_normalizer_of_commutator_le hJD.le hd)
  have hDx : D ≤ centralizer ({x} : Set M) := inf_le_left.trans (map_subtype_le _)
  have hDodd : Nat.Coprime 2 (Nat.card D) := by
    have h1 : Nat.card D ∣ Nat.card (pPrimeCore 2 (centralizer ({x} : Set M))) := by
      rw [← card_map_of_injective (centralizer ({x} : Set M)).subtype_injective]
      exact card_dvd_of_le inf_le_left
    exact (pPrimeCore_coprime_card (p := 2) (G := centralizer ({x} : Set M))).coprime_dvd_right h1
  have hDn : ∀ c ∈ centralizer ({x} : Set M) ⊓ normalizer (K : Set M), ∀ d ∈ D,
      c * d * c⁻¹ ∈ D := by
    intro c hc d hd
    obtain ⟨hcx, hcK⟩ := mem_inf.mp hc
    obtain ⟨hdO, hdK⟩ := mem_inf.mp hd
    obtain ⟨d', hd', rfl⟩ := hdO
    refine mem_inf.mpr ⟨⟨⟨c, hcx⟩ * d' * ⟨c, hcx⟩⁻¹, ?_, rfl⟩,
      mul_mem (mul_mem hcK hdK) (inv_mem hcK)⟩
    exact (pPrimeCore_normal (p := 2) (G := centralizer ({x} : Set M))).conj_mem d' hd' _
  have hKx : ⁅K, zpowers x⁆ = K :=
    commutator_eq_of_involution_mem hK (zpowers_le.mpr hxK)
      (commutator_mono hJK le_rfl (by rw [hJx]; exact hs)) hs2
  have hKD : ⁅K, D⁆ = K :=
    commutator_eq_of_involution_mem hK inf_le_right
      (commutator_mono hJK hD₀D (by rw [hJD]; exact hs)) hs2
  obtain ⟨B, _, _, hFs, hFna, ⟨eB⟩, z, hz2, hzO⟩ :=
    exists_unbalanced_almostSimple_of_hull hK hx hxK inf_le_right hDx hDodd hDn hKx hKD
  have : IsSimpleGroup (K ⧸ Open.fusionZStar K) := eB.symm.isSimpleGroup
  have hcatB : Blueprint.Catalog (GeneralizedFitting.subgroup B) :=
    SectionRank.catalog_of_mulEquiv eB (SectionRank.catalog_of_isKGroupCat_of_surjective hKM K
      (QuotientGroup.mk' (Open.fusionZStar K)) (QuotientGroup.mk'_surjective _))
  have hUL := TBLit.uList_of_uOutcome (hUc B hFs hFna hcatB ⟨z, hz2, hzO⟩)
  obtain ⟨eC⟩ := nonempty_fusionZStar_equiv_center K
  set e := eB.trans eC with hedef
  have hUS := TBLit.uList_of_mulEquiv e hUL
  have : IsSimpleGroup ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := e.symm.isSimpleGroup
  have hna : ∃ u v : (K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K), u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hFna
    exact ⟨e u, e v, fun h => huv (e.injective (by rw [map_mul, map_mul, h]))⟩
  rcases hUS with hodd | ⟨n, -, h7, ⟨θ⟩⟩ | hL | ⟨eH⟩
  · exact absurd hP34 (not_held_not_L34_of_properFixedComponent_oddLie hGLS hO hna hodd hPF).2
  · exact absurd hP34 (not_isL34Type_of_properFixedComponent_alternating (by omega) θ hPF)
  · exfalso
    have h1 := card_of_isL34Type hL
    have h2 := card_of_isL34Type hP34
    have h3 : Nat.card (P ⧸ Open.fusionZStar P) ≤ Nat.card P :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h4 : Nat.card P < Nat.card ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := by
      rw [← card_top (G := (K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K))]
      exact card_lt_of_lt (lt_top_iff_ne_top.mpr hPF.2.2.2)
    omega
  · obtain ⟨eH'⟩ := eH
    exact nonempty_pPrimeCore_quotient_equiv_held hHe hK eH'

theorem l34UnbalancedKGroupInput_of_catalogU
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hHe : TBLit.HeldTrivialMultiplier) :
    GrSLit.L34UnbalancedKGroupInput := by
  intro M _ _ hKM a x J hT hJL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ha, -, -, hJa, hJ, -, -⟩ := UnbalancedLayer.gsUnbalancingTriple_iff.mp hT
  obtain ⟨K, hK, hJK, hJp⟩ := UnbalancedLayer.two_layer_fixed_component_orbit_location ha hJa hJ
    (le_pLayer_of_isPComponent_centralizer ha hJa hJ)
  have hJC : J ≤ (K ⊔ conjugate K a) ⊓ centralizer ({a} : Set M) := le_inf hJK hJa
  by_cases hKa : conjugate K a = K
  swap
  ·
    obtain ⟨e⟩ := swap_case_type ha K hK (Ne.symm hKa) J hJC hJp
    exact ⟨K, hK, Or.inr (Or.inr ⟨LieType.CurtisTits.lieModel_of_mulEquiv e hJL, hKa,
      hJK.trans le_sup_left⟩)⟩
  obtain ⟨hle, -, heq⟩ :=
    UnbalancedGS.involution_orbit_fixed_component_quotient_comparison ha K hK _ rfl _ rfl J hJC hJp
  have hKK : K ⊔ conjugate K a = K := by rw [hKa, sup_idem]
  have hJK' : J ≤ K := by simpa only [hKK] using hJK
  have hJp' : IsPComponent 2 (J.subgroupOf (K ⊓ centralizer ({a} : Set M))) := by
    have h := hJp
    rw [hKK] at h
    exact h
  rcases hle.lt_or_eq with hlt | hle'
  ·
    exact ⟨K, hK, Or.inr (Or.inl ⟨nonempty_held_of_strict hUc hGLS hO hHe hKM hT hJL hK hKa hJK'
      hJp' hlt, hJK'.trans le_sup_left⟩)⟩
  ·
    have hcov := (heq hle').2 hKa.symm
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hJ
    have : Group.IsPerfect J :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJa).toMonoidHom)
        (subgroupOfEquivOfLe hJa).surjective
    have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
      CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hJa)
        (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hJ)
    obtain ⟨e⟩ := stable_case_type hK hJK' hJq hcov
    refine ⟨K, hK, Or.inl ⟨LieType.CurtisTits.lieModel_of_mulEquiv e hJL,
      le_antisymm (sup_le_sup_right hJK' _) (sup_le ?_ le_sup_right)⟩⟩
    calc K = J ⊔ (pPrimeCore 2 K).map K.subtype := hcov.symm
      _ ≤ J ⊔ pPrimeCore 2 M := sup_le_sup_left (map_pPrimeCore_le_of_isPComponent hK) _

end CFSG.ComponentClassification.CatLeaf
