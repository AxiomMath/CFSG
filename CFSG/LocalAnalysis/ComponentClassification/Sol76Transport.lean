module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21Rel
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')

theorem map_oddCoreIn (H : Subgroup G) :
    (oddCoreIn H).map φ.toMonoidHom = oddCoreIn (H.map φ.toMonoidHom) := by
  have h1 := pPrimeCore_map_iso 2 (H.equivMapOfInjective φ.toMonoidHom φ.injective)
  rw [oddCoreIn, oddCoreIn, ← h1, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_centralizer (S : Subgroup G) :
    (centralizer (S : Set G)).map φ.toMonoidHom =
      centralizer ((S.map φ.toMonoidHom : Subgroup G') : Set G') := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hg) s hs]
  · intro hx
    refine ⟨φ.symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro s hs
    apply φ.injective
    have h1 := (mem_centralizer_iff.mp hx) (φ s) ⟨s, hs, rfl⟩
    simpa using h1

theorem map_coreActionKernel (J : Subgroup G) :
    (coreActionKernel J).map φ.toMonoidHom = coreActionKernel (J.map φ.toMonoidHom) := by
  have hO : ((pPrimeCore 2 J).map J.subtype).map φ.toMonoidHom =
      (pPrimeCore 2 ↥(J.map φ.toMonoidHom)).map (J.map φ.toMonoidHom).subtype :=
    map_oddCoreIn φ J
  have hN := Subgroup.map_equiv_normalizer_eq J φ
  ext x
  constructor
  · rintro ⟨g, ⟨hgN, hg⟩, rfl⟩
    refine ⟨hN ▸ mem_map_of_mem _ hgN, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    rw [← hO]
    refine ⟨j⁻¹ * g⁻¹ * j * g, hg j hj, ?_⟩
    simp
  · intro hx
    obtain ⟨hxN, hx⟩ := hx
    refine ⟨φ.symm x, ⟨?_, fun j hj => ?_⟩, by simp⟩
    · rw [← hN] at hxN
      obtain ⟨g, hg, rfl⟩ := hxN
      simpa using hg
    · have h1 := hx (φ j) ⟨j, hj, rfl⟩
      rw [← hO] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = j⁻¹ * (φ.symm x)⁻¹ * j * φ.symm x := by
        apply φ.injective
        simpa using hyx
      rwa [← this]

theorem isTwoComponentIn_map {K Y : Subgroup G} (h : IsTwoComponentIn K Y) :
    IsTwoComponentIn (K.map φ.toMonoidHom) (Y.map φ.toMonoidHom) := by
  refine ⟨map_mono h.1, ?_⟩
  have h2 := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
    (Y.equivMapOfInjective φ.toMonoidHom φ.injective) h.2
  convert h2 using 1
  ext x
  constructor
  · intro hx
    rw [mem_subgroupOf] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    refine ⟨⟨k, h.1 hk⟩, hk, Subtype.ext ?_⟩
    rw [← hkx]
    rfl
  · rintro ⟨y, hy, rfl⟩
    rw [mem_subgroupOf]
    exact ⟨y, hy, rfl⟩

variable [Finite G] [Finite G']

theorem map_twoLayerIn (Y : Subgroup G) :
    (twoLayerIn Y).map φ.toMonoidHom = twoLayerIn (Y.map φ.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2
    (Y.equivMapOfInjective φ.toMonoidHom φ.injective)
  rw [twoLayerIn, twoLayerIn, ← h1, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem pRank_map (K : Subgroup G) :
    CFSG.pRank 2 ↥(K.map φ.toMonoidHom) = CFSG.pRank 2 ↥K := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact (SectionRank.pRank_top_eq_of_mulEquiv one_lt_two
    (K.equivMapOfInjective φ.toMonoidHom φ.injective)).symm

omit [Finite G] [Finite G'] in
theorem nonempty_quotient_fusionZStar_map (K : Subgroup G) :
    Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃*
      ↥(K.map φ.toMonoidHom) ⧸ Open.fusionZStar ↥(K.map φ.toMonoidHom)) := by
  let e := K.equivMapOfInjective φ.toMonoidHom φ.injective
  exact ⟨QuotientGroup.congr _ _ e (fusionZStar_map_mulEquiv e)⟩

omit [Finite G] [Finite G'] in
theorem isSolomonMember_map {L : Subgroup G} (h : IsSolomonMember L) :
    IsSolomonMember (L.map φ.toMonoidHom) := by
  obtain ⟨hL, T, hT1, hT2, hTK, hT⟩ := h
  refine ⟨?_, T.map φ.toMonoidHom, ?_, hT2.map _, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hL]
  · intro h1
    apply hT1
    rw [← LocalCores.map_map_symm φ T, h1, Subgroup.map_bot]
  · rw [← map_coreActionKernel]
    exact map_mono hTK
  · have h1 := isTwoComponentIn_map φ hT
    rwa [map_oddResidualIn _ φ.injective, Subgroup.map_sup, map_oddCoreIn, map_centralizer,
      Subgroup.map_inf_eq _ _ _ φ.injective, map_centralizer] at h1

theorem solomonLt_map {L K : Subgroup G} (h : SolomonLt L K) :
    SolomonLt (L.map φ.toMonoidHom) (K.map φ.toMonoidHom) := by
  obtain ⟨hL, hK, T, hT2, hTK, hT⟩ := h
  refine ⟨isSolomonMember_map φ hL, isSolomonMember_map φ hK, T.map φ.toMonoidHom, hT2.map _,
    ?_, ?_⟩
  · rw [← map_coreActionKernel]
    exact map_mono hTK
  · have h1 := isTwoComponentIn_map φ hT
    rwa [map_conjClosure, map_twoLayerIn, map_twoLayerIn, map_centralizer,
      Subgroup.map_inf_eq _ _ _ φ.injective, map_centralizer] at h1

theorem solomonLink_map {L K : Subgroup G} (h : SolomonLink L K) :
    SolomonLink (L.map φ.toMonoidHom) (K.map φ.toMonoidHom) := by
  obtain ⟨⟨e⟩, hlt⟩ := h
  obtain ⟨eL⟩ := nonempty_quotient_fusionZStar_map φ L
  obtain ⟨eK⟩ := nonempty_quotient_fusionZStar_map φ K
  exact ⟨⟨(eL.symm.trans e).trans eK⟩,
    hlt.imp (solomonLt_map φ) (solomonLt_map φ)⟩

theorem solomonEquiv_map {L K : Subgroup G} (h : SolomonEquiv L K) :
    SolomonEquiv (L.map φ.toMonoidHom) (K.map φ.toMonoidHom) :=
  ⟨isSolomonMember_map φ h.1, h.2.lift (fun M => M.map φ.toMonoidHom) fun _ _ => solomonLink_map φ⟩

theorem isSolomonMaximal_map {L : Subgroup G} (h : IsSolomonMaximal L) :
    IsSolomonMaximal (L.map φ.toMonoidHom) := by
  refine ⟨isSolomonMember_map φ h.1, fun K' K₁' hK' hlt => ?_⟩
  have h1 := solomonEquiv_map φ.symm hK'
  rw [LocalCores.map_map_symm] at h1
  have h2 := solomonLt_map φ.symm hlt
  have h3 := solomonEquiv_map φ (h.2 _ _ h1 h2)
  have hK : (K₁'.map φ.symm.toMonoidHom).map φ.toMonoidHom = K₁' := by
    simpa using LocalCores.map_map_symm φ.symm K₁'
  rwa [hK] at h3

theorem isSolomonWide_map {L : Subgroup G} (h : IsSolomonWide L) :
    IsSolomonWide (L.map φ.toMonoidHom) := by
  refine ⟨isSolomonMember_map φ h.1, fun K' hK' => ?_⟩
  have h1 := solomonEquiv_map φ.symm hK'
  rw [LocalCores.map_map_symm] at h1
  have h2 := h.2 _ h1
  rwa [pRank_map] at h2

theorem map_mem_solomonKStar {L : Subgroup G} (h : L ∈ solomonKStar G) :
    L.map φ.toMonoidHom ∈ solomonKStar G' :=
  ⟨isSolomonMaximal_map φ h.1, isSolomonWide_map φ h.2⟩

theorem map_solomonKStarOf (H : Subgroup G) :
    (solomonKStarOf H).map φ.toMonoidHom = solomonKStarOf (H.map φ.toMonoidHom) := by
  apply le_antisymm
  · rw [solomonKStarOf, Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK => ?_
    exact le_iSup₂_of_le (K.map φ.toMonoidHom)
      ⟨isTwoComponentIn_map φ hK.1, map_mem_solomonKStar φ hK.2⟩ le_rfl
  · refine iSup₂_le fun K' hK' => ?_
    have h1 := isTwoComponentIn_map φ.symm hK'.1
    have h2 := map_mem_solomonKStar φ.symm hK'.2
    rw [LocalCores.map_map_symm] at h1
    have h3 : K'.map φ.symm.toMonoidHom ≤ solomonKStarOf H := le_iSup₂_of_le _ ⟨h1, h2⟩ le_rfl
    have h4 := map_mono (f := φ.toMonoidHom) h3
    have hK : (K'.map φ.symm.toMonoidHom).map φ.toMonoidHom = K' := by
      simpa using LocalCores.map_map_symm φ.symm K'
    rwa [hK] at h4

theorem conjugate_mem_solomonKStar {L : Subgroup G} (h : L ∈ solomonKStar G) (g : G) :
    conjugate L g ∈ solomonKStar G :=
  map_mem_solomonKStar (MulAut.conj g⁻¹) h

theorem conjugate_solomonKStarOf (H : Subgroup G) (g : G) :
    conjugate (solomonKStarOf H) g = solomonKStarOf (conjugate H g) :=
  map_solomonKStarOf (MulAut.conj g⁻¹) H

omit φ [Group G'] [Finite G] in
theorem isPerfect_solomonKStarOf (H : Subgroup G) : Group.IsPerfect (solomonKStarOf H) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  unfold solomonKStarOf
  refine iSup₂_le fun K hK => ?_
  have hKK : ⁅K, K⁆ = K := hK.2.1.1.1
  rw [← hKK]
  exact commutator_mono (le_iSup₂_of_le K hK le_rfl) (le_iSup₂_of_le K hK le_rfl)

omit φ [Group G'] in
theorem normalizer_le_normalizer_solomonKStarOf (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (solomonKStarOf H : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (solomonKStarOf H).map (MulAut.conj g).toMonoidHom = solomonKStarOf H
  rw [map_solomonKStarOf (MulAut.conj g)]
  have hH : H.map (MulAut.conj g).toMonoidHom = H := mem_normalizer_iff_map_conj_eq.mp hg
  rw [hH]

end CFSG.ComponentClassification.Sol76
