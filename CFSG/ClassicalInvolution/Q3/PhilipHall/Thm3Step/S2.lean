module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43HsStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

namespace S2

section Transport

variable {G G' : Type} [Group G] [Group G'] (e : G ≃* G')

abbrev mapFam (Ω : Set (Subgroup G)) : Set (Subgroup G') :=
  (fun L : Subgroup G => L.map e.toMonoidHom) '' Ω

theorem map_symm_map (U : Subgroup G) : (U.map e.toMonoidHom).map e.symm.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem mapFam_symm_mapFam (Ω : Set (Subgroup G)) : mapFam e.symm (mapFam e Ω) = Ω := by
  ext L
  constructor
  · rintro ⟨_, ⟨M, hM, rfl⟩, rfl⟩
    show (M.map e.toMonoidHom).map e.symm.toMonoidHom ∈ Ω
    rwa [map_symm_map]
  · intro hL
    exact ⟨L.map e.toMonoidHom, ⟨L, hL, rfl⟩, map_symm_map e L⟩

variable {e}

theorem map_mem_RSet {Ω : Set (Subgroup G)} {R : Subgroup G} (hR : R ∈ RSet Ω) :
    R.map e.toMonoidHom ∈ RSet (mapFam e Ω) := by
  obtain ⟨J, hJ, hRJ, hR2, hmax⟩ := mem_RSet_iff.mp hR
  refine mem_RSet_iff.mpr ⟨J.map e.toMonoidHom, ⟨J, hJ, rfl⟩, Subgroup.map_mono hRJ,
    hR2.map _, fun R' hR'J hR'2 hle => ?_⟩
  have h1 : R'.comap e.toMonoidHom ≤ J := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hR'J hx
    have : z = x := e.injective (by simpa using hzx)
    rwa [← this]
  have h2 : IsPGroup 2 (R'.comap e.toMonoidHom) := hR'2.comap_of_injective _ e.injective
  have h3 : R ≤ R'.comap e.toMonoidHom := fun x hx => hle (Subgroup.mem_map_of_mem _ hx)
  have h4 := hmax _ h1 h2 h3
  calc R' = (R'.comap e.toMonoidHom).map e.toMonoidHom :=
        (Subgroup.map_comap_eq_self_of_surjective e.surjective R').symm
    _ = R.map e.toMonoidHom := by rw [h4]

theorem map_mem_USet {Ω : Set (Subgroup G)} {U : Subgroup G} (hU : U ∈ USet Ω) :
    U.map e.toMonoidHom ∈ USet (mapFam e Ω) := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  refine ⟨R.map e.toMonoidHom, map_mem_RSet hR, Subgroup.map_mono hUR, ?_, ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective U e.toMonoidHom e.injective)).mp hcyc
  · rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hidx

theorem inDistinctMembers_map {Ω : Set (Subgroup G)} {η : Set (Subgroup G)}
    (h : InDistinctMembers Ω η) : InDistinctMembers (mapFam e Ω) (mapFam e η) := by
  rintro _ ⟨U, hU, rfl⟩ _ ⟨U', hU', rfl⟩ hne _ ⟨J, hJ, rfl⟩ ⟨h1, h2⟩
  have hne' : U ≠ U' := fun h' => hne (by rw [h'])
  refine h U hU U' hU' hne' J hJ ⟨?_, ?_⟩
  · have := Subgroup.map_mono (f := e.symm.toMonoidHom) h1
    rwa [map_symm_map, map_symm_map] at this
  · have := Subgroup.map_mono (f := e.symm.toMonoidHom) h2
    rwa [map_symm_map, map_symm_map] at this

theorem map_mem_etaSet {Ω : Set (Subgroup G)} {S : Subgroup G} {η : Set (Subgroup G)}
    (h : η ∈ etaSet Ω S) : mapFam e η ∈ etaSet (mapFam e Ω) (S.map e.toMonoidHom) := by
  have hinj : Function.Injective (fun U : Subgroup G => U.map e.toMonoidHom) :=
    Subgroup.map_injective e.injective
  refine ⟨?_, inDistinctMembers_map h.2.1, fun η' hη' hd => ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨map_mem_USet (h.1 hU).1, Subgroup.map_mono (h.1 hU).2⟩
  · set η'' : Set (Subgroup G) := mapFam e.symm η' with hη''
    have hsub : η'' ⊆ {U | U ∈ USet Ω ∧ U ≤ S} := by
      rintro _ ⟨U, hU, rfl⟩
      refine ⟨?_, ?_⟩
      · have := map_mem_USet (e := e.symm) (hη' hU).1
        rwa [mapFam_symm_mapFam] at this
      · have := Subgroup.map_mono (f := e.symm.toMonoidHom) (hη' hU).2
        rwa [map_symm_map] at this
    have hd'' : InDistinctMembers Ω η'' := by
      have := inDistinctMembers_map (e := e.symm) hd
      rwa [mapFam_symm_mapFam] at this
    have hle := h.2.2 η'' hsub hd''
    have himg : mapFam e η'' = η' := by
      have := mapFam_symm_mapFam e.symm η'
      simpa using this
    have h1 : η'.ncard = η''.ncard := by
      rw [← himg, Set.ncard_image_of_injective _ hinj]
    rw [Set.ncard_image_of_injective _ hinj, h1]
    exact hle

theorem map_mem_WSet [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G} (hW : W ∈ WSet Ω) :
    W.map e.toMonoidHom ∈ WSet (mapFam e Ω) := by
  obtain ⟨η, ⟨S, hS, hinv⟩, rfl⟩ := hW
  let S' : Sylow 2 G' := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hS' : (S' : Subgroup G') = (S : Subgroup G).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  refine ⟨mapFam e η, ⟨S', ?_, ?_⟩, ?_⟩
  · rw [hS']
    exact map_mem_etaSet hS
  · intro s hs U hU
    rw [hS'] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    obtain ⟨U₀, hU₀, rfl⟩ := hU
    exact ⟨conjSub s₀ U₀, hinv s₀ hs₀ U₀ hU₀, (conjSub_map e.toMonoidHom s₀ U₀).symm⟩
  · simp only [Subgroup.map_iSup, iSup_image]

theorem WSet_map [Finite G] [Finite G'] (Ω : Set (Subgroup G)) :
    WSet (mapFam e Ω) = (fun W : Subgroup G => W.map e.toMonoidHom) '' WSet Ω := by
  ext W'
  constructor
  · intro hW'
    have h1 := map_mem_WSet (e := e.symm) hW'
    rw [mapFam_symm_mapFam] at h1
    refine ⟨_, h1, ?_⟩
    simpa using map_symm_map e.symm W'
  · rintro ⟨W, hW, rfl⟩
    exact map_mem_WSet hW

end Transport

section Rows

variable {X X' : Type} [Group X] [Group X']

theorem isL3E8_of_mulEquiv (e : X ≃* X') (h : IsL3E8 X) : IsL3E8 X' := by
  obtain ⟨E, hEn, hEab, hcard, ⟨q⟩⟩ := h
  haveI : (E.map e.toMonoidHom).Normal := hEn.map _ e.surjective
  have hEab' : IsElemAbelian 2 (E.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · rcases a with ⟨_, x₁, hx₁, rfl⟩
      rcases b with ⟨_, x₂, hx₂, rfl⟩
      apply Subtype.ext
      show e.toMonoidHom x₁ * e.toMonoidHom x₂ = e.toMonoidHom x₂ * e.toMonoidHom x₁
      rw [← map_mul, ← map_mul]
      congr 1
      have := hEab.1.1.comm ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
      simpa using congrArg Subtype.val this
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [← map_pow, hEab.2 x hx, map_one]
  refine ⟨E.map e.toMonoidHom, inferInstance, hEab', ?_, ⟨?_⟩⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hcard
  · exact (QuotientGroup.congr E (E.map e.toMonoidHom) e rfl).symm.trans q

variable {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y}

@[expose] noncomputable def subEquiv {P' : Subgroup H} {P : Subgroup Y}
    (hP : P'.map H.subtype = P) : ↥P' ≃* ↥P :=
  (P'.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hP)

@[expose] noncomputable def secQuotEquiv {P' : Subgroup H} {P : Subgroup Y}
    (hP : P'.map H.subtype = P) : FrameAEmptyPf.SecQuot P' ≃* FrameAEmptyPf.SecQuot P :=
  QuotientGroup.congr _ _ (subEquiv hP)
    (CFSG.ComponentClassification.OddCore.equiv_invariant (subEquiv hP))

theorem map_subEquiv_subgroupOf {P' : Subgroup H} {P : Subgroup Y} (hP : P'.map H.subtype = P)
    {M' : Subgroup H} (hM' : M' ≤ P') :
    (M'.subgroupOf P').map (subEquiv hP).toMonoidHom = (M'.map H.subtype).subgroupOf P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(y : H), Subgroup.mem_subgroupOf.mp hy, rfl⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨m, hm, hmx⟩ := hx
    refine ⟨⟨m, hM' hm⟩, Subgroup.mem_subgroupOf.mpr hm, Subtype.ext ?_⟩
    exact hmx

theorem restrictFamily_eq_mapFam {Φ : Set (Subgroup Y)} (hΦH : ∀ L ∈ Φ, L ≤ H) {P' : Subgroup H}
    {P : Subgroup Y} (hP : P'.map H.subtype = P) :
    restrictFamily Φ P = mapFam (subEquiv hP) (restrictFamily (restrictFamily Φ H) P') := by
  ext L₀
  constructor
  · rintro ⟨L, hL, hLP, rfl⟩
    have hLH := hΦH L hL
    have hLP' : L.subgroupOf H ≤ P' := by
      intro x hx
      have hxP : ((x : H) : Y) ∈ P := hLP (Subgroup.mem_subgroupOf.mp hx)
      rw [← hP] at hxP
      obtain ⟨y, hy, hyx⟩ := hxP
      have : y = x := H.subtype_injective hyx
      rwa [← this]
    refine ⟨(L.subgroupOf H).subgroupOf P',
      ⟨L.subgroupOf H, subgroupOf_mem_restrictFamily hL hLH, hLP', rfl⟩, ?_⟩
    show ((L.subgroupOf H).subgroupOf P').map (subEquiv hP).toMonoidHom = L.subgroupOf P
    rw [map_subEquiv_subgroupOf hP hLP', Subgroup.map_subgroupOf_eq_of_le hLH]
  · rintro ⟨_, ⟨M', hM', hM'P', rfl⟩, rfl⟩
    refine ⟨M'.map H.subtype, mem_restrictFamily_iff.mp hM', ?_, ?_⟩
    · rw [← hP]
      exact Subgroup.map_mono hM'P'
    · exact map_subEquiv_subgroupOf hP hM'P'

theorem oddQuotientFamily_eq_mapFam {Φ : Set (Subgroup Y)} (hΦH : ∀ L ∈ Φ, L ≤ H)
    {P' : Subgroup H} {P : Subgroup Y} (hP : P'.map H.subtype = P) :
    oddQuotientFamily (restrictFamily Φ P) =
      mapFam (secQuotEquiv hP) (oddQuotientFamily (restrictFamily (restrictFamily Φ H) P')) := by
  rw [restrictFamily_eq_mapFam hΦH hP]
  unfold oddQuotientFamily mapFam
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr fun L _ => ?_
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem thm3RowsA_of_restrict {Φ : Set (Subgroup Y)} (hΦH : ∀ L ∈ Φ, L ≤ H) {P' : Subgroup H}
    {P : Subgroup Y} (hP : P'.map H.subtype = P) (h : Thm3RowsA (restrictFamily Φ H) P') :
    Thm3RowsA Φ P := by
  set E := secQuotEquiv hP with hE
  rcases h with ⟨N, hN, hidx, hLie⟩ | hM | hL | hW
  · haveI := hN
    haveI : (N.map E.toMonoidHom).Normal := hN.map _ E.surjective
    refine Or.inl ⟨N.map E.toMonoidHom, inferInstance, ?_, ?_⟩
    · exact (Subgroup.index_map_equiv N E).trans hidx
    · exact CFSG.Blueprint.LieModel.of_mulEquiv
        (N.equivMapOfInjective E.toMonoidHom E.injective) hLie
  · obtain ⟨e⟩ : Nonempty (FrameAEmptyPf.SecQuot P' ≃*
        CFSG.Blueprint.NativeSporadic.Carrier .M12) := hM
    exact Or.inr (Or.inl ⟨E.symm.trans e⟩)
  · exact Or.inr (Or.inr (Or.inl (isL3E8_of_mulEquiv E hL)))
  · obtain ⟨W, hW, hWset, ⟨d⟩⟩ := hW
    haveI := hW
    haveI : (W.map E.toMonoidHom).Normal := hW.map _ E.surjective
    refine Or.inr (Or.inr (Or.inr ⟨W.map E.toMonoidHom, inferInstance, ?_, ⟨?_⟩⟩))
    · rw [oddQuotientFamily_eq_mapFam hΦH hP, WSet_map, hWset, Set.image_singleton]
    · exact (QuotientGroup.congr W (W.map E.toMonoidHom) E rfl).symm.trans d

theorem thm3RowsG_of_restrict {Φ : Set (Subgroup Y)} (hΦH : ∀ L ∈ Φ, L ≤ H) {P' : Subgroup H}
    {P : Subgroup Y} (hP : P'.map H.subtype = P) (h : Thm3RowsG (restrictFamily Φ H) P') :
    Thm3RowsG Φ P := by
  rcases h with hG | hA
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv (secQuotEquiv hP) hG)
  · exact Or.inr (thm3RowsA_of_restrict hΦH hP hA)

end Rows

section Restrict

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {H : Subgroup Y}

theorem image_map_image_subgroupOf {S : Set (Subgroup Y)} (hS : ∀ L ∈ S, L ≤ H) :
    (fun L' : Subgroup H => L'.map H.subtype) '' ((fun L : Subgroup Y => L.subgroupOf H) '' S) =
      S := by
  ext L
  constructor
  · rintro ⟨_, ⟨M, hM, rfl⟩, rfl⟩
    show (M.subgroupOf H).map H.subtype ∈ S
    rwa [Subgroup.map_subgroupOf_eq_of_le (hS M hM)]
  · intro hL
    exact ⟨L.subgroupOf H, ⟨L, hL, rfl⟩, Subgroup.map_subgroupOf_eq_of_le (hS L hL)⟩

theorem mem_restrict_iff {L : Subgroup Y} (hL : L ≤ H) :
    L.subgroupOf H ∈ restrictFamily Φ H ↔ L ∈ Φ := by
  constructor
  · intro h
    have := mem_restrictFamily_iff.mp h
    rwa [Subgroup.map_subgroupOf_eq_of_le hL] at this
  · exact fun h => subgroupOf_mem_restrictFamily h hL

theorem twinSet_restrict_iff {M L : Subgroup Y} (hM : M ≤ H) (hL : L ≤ H) :
    L.subgroupOf H ∈ twinSet (restrictFamily Φ H) (M.subgroupOf H) ↔ L ∈ twinSet Φ M := by
  constructor
  · rintro ⟨hLΦ, w, hwM, hwL⟩
    exact ⟨(mem_restrict_iff hL).mp hLΦ, (w : Y), isUniqueInvolution_of_subgroupOf hwM hM,
      isUniqueInvolution_of_subgroupOf hwL hL⟩
  · exact twinSet_subgroupOf hM hL

theorem omegaNbr_restrict_iff (hΦ : HypOmegaGen Φ) {M L : Subgroup Y} (hM : M ≤ H)
    (hL : L ≤ H) :
    L.subgroupOf H ∈ omegaNbr (restrictFamily Φ H) (M.subgroupOf H) ↔ L ∈ omegaNbr Φ M :=
  ⟨omegaNbr_of_restrict hM hL, fun h => E187C.omegaNbr_subgroupOf_of
    (fun hJ hT hTJ => Sec6Gen.isSylow2In_of_mem_RSet_of_le hΦ hJ hT hTJ) hM hL h.1 h⟩

theorem aGraphAdj_restrict (hΦ : HypOmegaGen Φ) {B C : Subgroup Y} (hB : B ≤ H) (hC : C ≤ H)
    (h : aGraphAdj Φ B C) : aGraphAdj (restrictFamily Φ H) (B.subgroupOf H) (C.subgroupOf H) := by
  obtain ⟨hCΦ, ⟨zb, zc, hv⟩ | ⟨zc, zb, hv⟩ | ⟨htw, hne⟩⟩ := h
  · exact ⟨subgroupOf_mem_restrictFamily hCΦ hC,
      Or.inl ⟨_, _, aViol_restrict_gen hΦ hB hC hv⟩⟩
  · exact ⟨subgroupOf_mem_restrictFamily hCΦ hC,
      Or.inr (Or.inl ⟨_, _, aViol_restrict_gen hΦ hC hB hv⟩)⟩
  · exact ⟨subgroupOf_mem_restrictFamily hCΦ hC,
      Or.inr (Or.inr ⟨twinSet_subgroupOf hB hC htw, subgroupOf_ne_of_ne hB hC hne⟩)⟩

theorem subgroupOf_mem_aStar (hΦ : HypOmegaGen Φ) (hΦH : ∀ L ∈ Φ, L ≤ H) {K : Subgroup Y}
    (hK : K ∈ Φ) {L : Subgroup Y} (hL : L ∈ aStar Φ K) :
    L.subgroupOf H ∈ aStar (restrictFamily Φ H) (K.subgroupOf H) := by
  induction hL with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    rename_i b c
    exact ih.tail (aGraphAdj_restrict hΦ (hΦH b (T3Core.mem_of_mem_aStar hK hab)) (hΦH c hbc.1) hbc)

theorem aStar_eq_image (hΦ : HypOmegaGen Φ) (hΦH : ∀ L ∈ Φ, L ≤ H) {K : Subgroup Y}
    (hK : K ∈ Φ) :
    aStar Φ K = (fun L' : Subgroup H => L'.map H.subtype) ''
      aStar (restrictFamily Φ H) (K.subgroupOf H) := by
  ext L
  constructor
  · intro hL
    exact ⟨L.subgroupOf H, subgroupOf_mem_aStar hΦ hΦH hK hL,
      Subgroup.map_subgroupOf_eq_of_le (hΦH L (T3Core.mem_of_mem_aStar hK hL))⟩
  · rintro ⟨L', hL', rfl⟩
    exact mem_aStar_of_restrict_gen hΦ (hΦH K hK) hL'

theorem map_omegaGen_aStar (hΦ : HypOmegaGen Φ) (hΦH : ∀ L ∈ Φ, L ≤ H) {K : Subgroup Y}
    (hK : K ∈ Φ) :
    (omegaGen (aStar (restrictFamily Φ H) (K.subgroupOf H))).map H.subtype =
      omegaGen (aStar Φ K) := by
  rw [aStar_eq_image hΦ hΦH hK]
  unfold omegaGen
  simp only [Subgroup.map_iSup, iSup_image]

theorem omegaOfSet_twinSet_restrict (hΦ : HypOmegaGen Φ) (hΦH : ∀ L ∈ Φ, L ≤ H) {M : Subgroup Y}
    (hM : M ≤ H) :
    omegaOfSet (restrictFamily Φ H) (twinSet (restrictFamily Φ H) (M.subgroupOf H)) =
      (fun L : Subgroup Y => L.subgroupOf H) '' omegaOfSet Φ (twinSet Φ M) := by
  ext N'
  constructor
  · rintro ⟨hN', hall⟩
    have hNΦ : N'.map H.subtype ∈ Φ := mem_restrictFamily_iff.mp hN'
    have hNH := hΦH _ hNΦ
    refine ⟨N'.map H.subtype, ⟨hNΦ, fun T hT => ?_⟩, subgroupOf_map_subtype' N'⟩
    have hTH := hΦH T hT.1
    have hT' := (twinSet_restrict_iff (Φ := Φ) hM hTH).mpr hT
    have h1 := hall _ hT'
    rw [← subgroupOf_map_subtype' N'] at h1
    exact (omegaNbr_restrict_iff hΦ hTH hNH).mp h1
  · rintro ⟨N, ⟨hNΦ, hall⟩, rfl⟩
    have hNH := hΦH N hNΦ
    refine ⟨subgroupOf_mem_restrictFamily hNΦ hNH, fun T' hT' => ?_⟩
    have hTΦ : T'.map H.subtype ∈ Φ := mem_restrictFamily_iff.mp hT'.1
    have hTH := hΦH _ hTΦ
    rw [← subgroupOf_map_subtype' T'] at hT' ⊢
    exact (omegaNbr_restrict_iff hΦ hTH hNH).mpr (hall _ ((twinSet_restrict_iff hM hTH).mp hT'))

theorem mem_vStar_iff (hΦ : HypOmegaGen Φ) (hΦH : ∀ L ∈ Φ, L ≤ H) {K L : Subgroup Y}
    (hKH : K ≤ H) (hLH : L ≤ H) :
    L.subgroupOf H ∈ vStar (restrictFamily Φ H) (K.subgroupOf H) ↔ L ∈ vStar Φ K := by
  have hsub : ∀ M : Subgroup Y, ∀ N ∈ omegaOfSet Φ (twinSet Φ M), N ≤ H :=
    fun M N hN => hΦH N hN.1
  constructor
  · rintro ⟨hLΦ, heq⟩
    refine ⟨(mem_restrict_iff hLH).mp hLΦ, ?_⟩
    rw [omegaOfSet_twinSet_restrict hΦ hΦH hKH, omegaOfSet_twinSet_restrict hΦ hΦH hLH] at heq
    have := congrArg (fun S : Set (Subgroup H) => (fun L' : Subgroup H => L'.map H.subtype) '' S)
      heq
    rwa [image_map_image_subgroupOf (hsub K), image_map_image_subgroupOf (hsub L)] at this
  · rintro ⟨hLΦ, heq⟩
    refine ⟨(mem_restrict_iff hLH).mpr hLΦ, ?_⟩
    rw [omegaOfSet_twinSet_restrict hΦ hΦH hKH, omegaOfSet_twinSet_restrict hΦ hΦH hLH, heq]

theorem map_oddCoreOf_subgroupOf {L : Subgroup Y} (hL : L ≤ H) :
    (oddCoreOf (L.subgroupOf H)).map H.subtype = oddCoreOf L := by
  rw [oddCoreOf_subgroupOf hL,
    Subgroup.map_subgroupOf_eq_of_le ((oddCoreOf_le_self L).trans hL)]

end Restrict

end S2

open S2

theorem thm3RLiftSub_proved : Thm3RLiftSub := by
  intro Y _ _ Φ hΦ K hK _ hC
  set H := omegaGen Φ with hHdef
  have hΦH : ∀ L ∈ Φ, L ≤ H := fun L hL => le_omegaGen hL
  have hKH : K ≤ H := hΦH K hK
  have hΩ : HypOmegaGen Φ := hΦ.hyp
  obtain ⟨⟨heq, hcomm⟩, hrows⟩ := hC
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext L
    constructor
    · intro hL
      have hLH := hΦH L (T3Core.mem_of_mem_aStar hK hL)
      have h1 := subgroupOf_mem_aStar hΩ hΦH hK hL
      rw [heq] at h1
      exact (mem_vStar_iff hΩ hΦH hKH hLH).mp h1
    · intro hL
      have hLH := hΦH L hL.1
      have h1 := (mem_vStar_iff hΩ hΦH hKH hLH).mpr hL
      rw [← heq] at h1
      have h2 := mem_aStar_of_restrict_gen hΩ hKH h1
      rwa [Subgroup.map_subgroupOf_eq_of_le hLH] at h2
  · intro L hL hLV M hM
    have hLH := hΦH L hL
    have hMH := hΦH M hM.1
    have h1 := hcomm _ (subgroupOf_mem_restrictFamily hL hLH)
      (fun h => hLV ((mem_vStar_iff hΩ hΦH hKH hLH).mp h)) _
      ((mem_vStar_iff hΩ hΦH hKH hMH).mpr hM)
    have h2 := Subgroup.map_mono (f := H.subtype) h1
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLH,
      Subgroup.map_subgroupOf_eq_of_le hMH] at h2
    refine h2.trans ((Subgroup.map_inf_le _ _ _).trans ?_)
    rw [map_oddCoreOf_subgroupOf hLH, map_oddCoreOf_subgroupOf hMH]
  · exact thm3RowsG_of_restrict hΦH (map_omegaGen_aStar hΩ hΦH hK) hrows

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
