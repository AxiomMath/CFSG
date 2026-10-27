module

public import CFSG.LocalAnalysis.ComponentClassification.GSTopExclusion
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMReach
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamilyOfEverySource

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrRankIncrease
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gsWeakMaximalComponent_of_gsMirrorReach_of_noSwap {T : Type*} [Group T]
    (hsw : ∀ (z s : G) (Y : Subgroup G), orderOf z = 2 → orderOf s = 2 → z * s = s * z →
      IsTwoComponentIn Y (centralizer ({z} : Set G)) → GrSLit.GSWeakMaximalComponent Y →
      Nonempty (Y ⧸ Open.fusionZStar Y ≃* T) → conjugate Y s ≠ Y → False)
    {Y J : Subgroup G} (hY : GrSLit.GSWeakMaximalComponent Y)
    (hYT : Nonempty (Y ⧸ Open.fusionZStar Y ≃* T)) (hR : GSMirrorReach Y J) :
    GrSLit.GSWeakMaximalComponent J ∧ Nonempty (J ⧸ Open.fusionZStar J ≃* T) := by
  induction hR with
  | refl => exact ⟨hY, hYT⟩
  | @tail M X _ hst ih =>
    obtain ⟨hM, ⟨e⟩⟩ := ih
    rcases hst with ⟨c, d, hC⟩ | hMX | ⟨g, rfl⟩
    · have hR1 : GrSLit.GSWeakReach M X := Relation.ReflTransGen.single ⟨c, d, hC⟩
      obtain ⟨e'⟩ := hM.2 X hR1
      exact ⟨hM.of_weakReach hR1, ⟨e'.symm.trans e⟩⟩
    · obtain ⟨z, s, D, hz, hs, hzs, hMz, hMs, -⟩ := hMX
      exact (hsw z s M hz hs hzs hMz hM ⟨e⟩ hMs).elim
    · obtain ⟨e'⟩ := GrSLit.nonempty_fusionZStar_equiv_conjugate M g
      exact ⟨Foote5.SolMax.gsWeakMaximalComponent_conjugate hM g, ⟨e'.symm.trans e⟩⟩

theorem mem_footeFamilyOf_of_gsWeakMaximalComponent {L Y : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hYz : IsTwoComponentIn Y (centralizer ({z} : Set G)))
    (hY : GrSLit.GSWeakMaximalComponent Y)
    (hYT : Nonempty (Y ⧸ Open.fusionZStar Y ≃* L ⧸ Open.fusionZStar L)) :
    Y ∈ footeFamilyOf L :=
  ⟨⟨z, footePointedMaximal_of_gsWeakMaximalComponent hY ⟨hz, hYz.1, hYz.2⟩⟩, hYT⟩

@[expose] def FooteGSMaximalSwapExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → IsSimpleGroup G →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    ∀ (z s : G) (Y : Subgroup G), orderOf z = 2 → orderOf s = 2 → z * s = s * z →
      IsTwoComponentIn Y (centralizer ({z} : Set G)) → GrSLit.GSWeakMaximalComponent Y →
      Nonempty (Y ⧸ Open.fusionZStar Y ≃* L ⧸ Open.fusionZStar L) → conjugate Y s ≠ Y → False

@[expose] def FooteGSMaximalRepresentative : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → IsSimpleGroup G →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    ∀ A ∈ footeFamilyOf L, ∃ Y : Subgroup G, GrSLit.GSWeakMaximalComponent Y ∧
      Nonempty (Y ⧸ Open.fusionZStar Y ≃* L ⧸ Open.fusionZStar L) ∧ GSMirrorReach Y A

theorem gsWeakMaximalComponent_of_mem_footeFamilyOf_of_gsMirrorReach
    (hsw : FooteGSMaximalSwapExclusion) (hrep : FooteGSMaximalRepresentative) {t : G}
    {L : Subgroup G} (hmin : FooteMinimal G) (hce : FooteCounterexample G t L)
    (hsimp : IsSimpleGroup G) (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2)
    {A J : Subgroup G} (hAF : A ∈ footeFamilyOf L) (hAJ : GSMirrorReach A J) :
    GrSLit.GSWeakMaximalComponent J ∧
      Nonempty (J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L) := by
  obtain ⟨Y, hY, hYT, hYA⟩ := hrep G t L hmin hce hsimp hrank2 A hAF
  exact gsWeakMaximalComponent_of_gsMirrorReach_of_noSwap (hsw G t L hmin hce hsimp hrank2) hY
    hYT (Relation.ReflTransGen.trans hYA hAJ)

theorem footeTopExclusion_of_gsMaximalSwap (hsw : FooteGSMaximalSwapExclusion)
    (hrep : FooteGSMaximalRepresentative) : Foote5.SolMax.FooteTopExclusion := by
  intro G _ _ t L hmin hce hsimp hrank2 A hAF J hAJ _ hlt
  obtain ⟨-, ⟨eJ⟩⟩ := gsWeakMaximalComponent_of_mem_footeFamilyOf_of_gsMirrorReach hsw hrep hmin
    hce hsimp hrank2 hAF hAJ
  obtain ⟨eA⟩ := hAF.2
  exact absurd (Nat.card_congr (eA.trans eJ.symm).toEquiv) (ne_of_lt hlt)

@[expose] def FooteRankIncrease : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → IsSimpleGroup G →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    ∀ (a : G) (J S : Subgroup G), FootePointedMaximal a J →
      Nonempty (J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L) →
      S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
      (∃ P : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
        (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) →
      ∀ (b : G) (K : Subgroup G), orderOf b = 2 → b ∈ S ⊓ UnbalancedLayer.coreActionKernel J →
        GrSLit.GSWeakCorr a J b K →
        ¬ (conjugate K a = K ∧
          UnbalancedGS.gsFixedLayer J b ⊔ (pPrimeCore 2 K).map K.subtype = K) →
        ∃ (e : G) (K' : Subgroup G), orderOf e = 2 ∧
          e ∈ S ⊓ UnbalancedLayer.coreActionKernel J ∧ GrSLit.GSWeakCorr a J e K' ∧
          conjugate K' a ≠ K' ∧
          CFSG.pRank 2 ↥(centralizer ({a} : Set G) ⊓ UnbalancedLayer.coreActionKernel J) <
            CFSG.pRank 2 ↥(centralizer ({e} : Set G) ⊓ UnbalancedLayer.coreActionKernel K')

omit [Finite G] in
theorem centralizer_inf_normalizer_inf_coreActionKernel (a : G) (J : Subgroup G) :
    centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ UnbalancedLayer.coreActionKernel J =
      centralizer ({a} : Set G) ⊓ UnbalancedLayer.coreActionKernel J := by
  have h : normalizer (J : Set G) ⊓ UnbalancedLayer.coreActionKernel J =
      UnbalancedLayer.coreActionKernel J :=
    inf_eq_right.mpr fun _ hx => (UnbalancedLayer.mem_coreActionKernel.mp hx).1
  rw [inf_assoc, h]

theorem eq_of_gsWeakCorr_self {a : G} {J K : Subgroup G} (h : GrSLit.GSWeakCorr a J a K) :
    K = J := by
  obtain ⟨ha, -, -, hJa, hJpc, hKa, hKpc, hbN, hbO, hTK⟩ := h
  have hJK := Foote5.SolMax.sup_conjugate_eq_of_fixedLayer ha ha rfl hJa hJpc hKa hKpc
    ⟨ha, hJa, hJpc⟩ hbN hbO hTK
    ((UnbalancedGS.gsFixedLayer_le_inf _ a).trans (inf_le_left.trans le_sup_left))
  rw [UnbalancedCorr.conjugate_eq_self_of_le_centralizer hJa,
    UnbalancedCorr.conjugate_eq_self_of_le_centralizer hKa, sup_idem, sup_idem] at hJK
  exact hJK.symm

theorem gsIsoCorr_of_gsWeakCorr {a b : G} {J K : Subgroup G} (h : GrSLit.GSWeakCorr a J b K)
    (hKa : conjugate K a = K)
    (hsup : UnbalancedGS.gsFixedLayer J b ⊔ (pPrimeCore 2 K).map K.subtype = K) :
    UnbalancedGS.GSIsoCorr a J b K := by
  have hD := Foote5.SolMax.gsFixedLayer_common_component_of_gsWeakCorr h
  obtain ⟨ha, hb, hab, hJa, hJp, hKb, hKp, hbN, hbO, hTK⟩ := h
  have hTK' : UnbalancedGS.gsFixedLayer J b ≤ K := by
    rw [hKa, sup_idem] at hTK
    exact hTK
  have haN : a ∈ normalizer (K : Set G) := UnbalancedLayer.mem_normalizer_of_conjugate_eq hKa
  have haD : a ∈ UnbalancedLayer.coreActionKernel (UnbalancedGS.gsFixedLayer J b) :=
    GSLit.mem_coreActionKernel_of_le_centralizer
      ((UnbalancedGS.gsFixedLayer_le_inf J b).trans (inf_le_left.trans hJa))
  have haK : a ∈ UnbalancedLayer.coreActionKernel K := mem_coreActionKernel_of_sup hTK' hsup haN haD
  have hFix : UnbalancedGS.gsFixedLayer K a = UnbalancedGS.gsFixedLayer J b :=
    Foote5.SolMax.gsFixedLayer_eq_of_common_component ha ⟨hKb, hKp⟩ hab hKa haK hD hTK'
  rw [UnbalancedGS.gsIsoCorr_iff_sup]
  refine ⟨⟨ha, hb, hab, hJa, hJp, hKb, hKp, hbN, hbO, ?_⟩, by rw [hKa, sup_idem], hsup⟩
  rw [hKa, sup_idem, hFix]

theorem footeRankIncrease_of_smallCovers
    (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) : FooteRankIncrease := by
  intro X _ _ t L hmin hce hsimp hrank2 a J S hJp hJT hSH hSsyl b K hb hbP hC hnot
  have hJF : J ∈ footeFamilyOf L := ⟨⟨a, hJp⟩, hJT⟩
  have hLfam : FooteFamilyType L := hce.1.2.2.2.2.1
  obtain ⟨-, eJT⟩ := isSimpleGroup_quotient_of_mem_footeFamilyOf hGA hGC hSA hLfam hrank2
    hJp.1 hJF
  have hfixed : ∀ (e : X) (M : Subgroup X), GrSLit.GSWeakCorr a J e M →
      (pPrimeCore 2 J).index = (pPrimeCore 2 M).index := by
    intro e M hCM
    by_cases hae : a = e
    · subst e
      rw [eq_of_gsWeakCorr_self hCM]
    · have hpt := Foote5.SolMax.footePointedStep_of_gsWeakCorr hCM hae
      have hreach := FootePointedReach.single hpt
      obtain ⟨eJM⟩ := hJp.2 e M hreach
      have hMF : M ∈ footeFamilyOf L :=
        ⟨⟨e, hJp.of_reach hreach⟩, ⟨eJM.symm.trans hJT.some⟩⟩
      obtain ⟨-, eMT⟩ := isSimpleGroup_quotient_of_mem_footeFamilyOf hGA hGC hSA hLfam
        hrank2 hpt.2.1 hMF
      rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
      exact Nat.card_congr (eJT.some.trans eMT.some.symm).toEquiv
  apply GrSLit.fixed_source_rank_increase_of_index_eq hJp.1.1 hJp.1.2.1 hJp.1.2.2
    (by rw [hrank2 J hJF]) hfixed hSH hSsyl hbP hC
  intro hiso
  obtain ⟨-, hpair, hcover⟩ := UnbalancedGS.gsIsoCorr_iff_sup.mp hiso
  have hKa : conjugate K a = K := by
    have hle : conjugate K a ≤ K := le_sup_right.trans hpair.le
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective]
  exact hnot ⟨hKa, hcover⟩

theorem footeRankIncrease_holds
 : FooteRankIncrease :=
  footeRankIncrease_of_smallCovers TBLit.griessMultipliersAllModels_holds
    @Milestones.cl_lit_griess_schur_multipliers_central_covers
    Alternating.Multipliers.schurAlternatingMultiplierInput

theorem footeGSMaximalRepresentative_of_rankIncrease (hRI : FooteRankIncrease) :
    FooteGSMaximalRepresentative := by
  intro G _ _ t L hmin hce hsimp hrank2 A hAF
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨⟨z, hzA⟩, hAT⟩ := hAF
  let R : Set (G × Subgroup G) := {p | FootePointedMaximal p.1 p.2 ∧
    Nonempty (p.2 ⧸ Open.fusionZStar p.2 ≃* L ⧸ Open.fusionZStar L) ∧ GSMirrorReach p.2 A}
  obtain ⟨⟨a, Y⟩, ⟨hYp, hYT, hYA⟩, hmax⟩ := Set.exists_max_image R
    (fun p : G × Subgroup G => toLex
      (CFSG.pRank 2 ↥(centralizer ({p.1} : Set G) ⊓ normalizer (p.2 : Set G) ⊓
        UnbalancedLayer.coreActionKernel p.2),
      2 ^ (Nat.card ↥(centralizer ({p.1} : Set G) ⊓ normalizer (p.2 : Set G))).factorization 2))
    (Set.toFinite R) ⟨(z, A), hzA, hAT, GSMirrorReach.refl A⟩
  have hstep : ∀ (b : G) (K : Subgroup G), GrSLit.GSWeakCorr a Y b K → a ≠ b → (b, K) ∈ R := by
    intro b K hC hab
    have hpt := Foote5.SolMax.footePointedStep_of_gsWeakCorr hC hab
    obtain ⟨eYK⟩ := hYp.2 b K (FootePointedReach.single hpt)
    exact ⟨hYp.of_reach (FootePointedReach.single hpt), ⟨eYK.symm.trans hYT.some⟩,
      Relation.ReflTransGen.trans (Foote5.SolMax.gsMirrorReach_reverse_of_gsWeakCorr hC ⟨eYK⟩)
        hYA⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (Y : Set G))) :=
    inferInstance
  set S : Subgroup G := (P₀ : Subgroup _).map
    (centralizer ({a} : Set G) ⊓ normalizer (Y : Set G)).subtype with hSdef
  have hSH : S ≤ centralizer ({a} : Set G) ⊓ normalizer (Y : Set G) := map_subtype_le _
  have hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (Y : Set G)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (Y : Set G)) :=
    ⟨P₀, (comap_map_eq_self_of_injective
      (centralizer ({a} : Set G) ⊓ normalizer (Y : Set G)).subtype_injective _).symm⟩
  have hall : ∀ b ∈ S ⊓ UnbalancedLayer.coreActionKernel Y, orderOf b = 2 →
      ∃ K : Subgroup G, UnbalancedGS.GSIsoCorr a Y b K := by
    intro b hbP hb
    by_cases hba : b = a
    · obtain rfl := hba
      exact ⟨Y, GSLit.gsIsoCorr_self hYp.1.1 hYp.1.2.1 hYp.1.2.2⟩
    by_contra hno
    have hbY : b ∈ UnbalancedLayer.coreActionKernel Y := (mem_inf.mp hbP).2
    have hab : a * b = b * a :=
      (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH (mem_inf.mp hbP).1)).1).symm
    obtain ⟨K, hKb, -, hTK, -⟩ :=
      exists_footeStep footeLBalanceInput_holds hYp.1 hb hab (Ne.symm hba) hbY
    obtain ⟨hbN, hbO⟩ := UnbalancedLayer.mem_coreActionKernel.mp hbY
    have hC : GrSLit.GSWeakCorr a Y b K :=
      ⟨hYp.1.1, hb, hab, hYp.1.2.1, hYp.1.2.2, hKb.2.1, hKb.2.2, hbN, hbO, hTK⟩
    obtain ⟨e, K', -, -, hC', hK'a, hlt⟩ := hRI G t L hmin hce hsimp hrank2 a Y S hYp hYT hSH
      hSsyl b K hb hbP hC (fun h => hno ⟨K, gsIsoCorr_of_gsWeakCorr hC h.1 h.2⟩)
    have hae : a ≠ e := by
      rintro rfl
      exact hK'a (UnbalancedCorr.conjugate_eq_self_of_le_centralizer hC'.2.2.2.2.2.1)
    have hle := hmax _ (hstep e K' hC' hae)
    rw [← centralizer_inf_normalizer_inf_coreActionKernel,
      ← centralizer_inf_normalizer_inf_coreActionKernel] at hlt
    obtain ⟨hle1, -⟩ := Prod.Lex.toLex_le_toLex'.mp hle
    exact absurd hle1 (not_le.mpr hlt)
  have hcentral : ∀ (b : G) (K : Subgroup G), orderOf b = 2 →
      b ∈ centralizer ({a} : Set G) ⊓ normalizer (Y : Set G) →
      (∀ j ∈ Y, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 Y).map Y.subtype) →
      UnbalancedGS.GSIsoCorr a Y b K → b ∈ S → (∀ s ∈ S, s * b = b * s) →
      S ≤ centralizer ({b} : Set G) ⊓ normalizer (K : Set G) ∧
        ∃ P : Sylow 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (K : Set G)),
          (P : Subgroup _) = S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (K : Set G)) := by
    intro b K _ _ _ hK _ hbZ
    have hSb : S ≤ centralizer ({b} : Set G) := fun s hs =>
      mem_centralizer_singleton_iff.mpr (hbZ s hs)
    obtain ⟨-, -, -, -, -, -, -, -, hgrow⟩ :=
      UnbalancedLayer.isomorphic_correspondence_sylow_growth hK rfl rfl rfl rfl
    obtain ⟨hSHL, hρ, -, hstrict, -⟩ := hgrow S hSH hSsyl hSb
    refine ⟨hSHL, ?_⟩
    by_contra hns
    have hν := hstrict hns
    have hCK : GrSLit.GSWeakCorr a Y b K :=
      GrSLit.GSWeakCorr.of_gsCorr (UnbalancedGS.gsIsoCorr_iff_sup.mp hK).1
    by_cases hba : b = a
    · obtain rfl := hba
      obtain rfl := eq_of_gsWeakCorr_self hCK
      exact lt_irrefl _ hν
    · have hle := hmax _ (hstep b K hCK (Ne.symm hba))
      obtain ⟨hle1, hle2⟩ := Prod.Lex.toLex_le_toLex'.mp hle
      exact absurd (hle2 (le_antisymm hle1 hρ)) (not_le.mpr hν)
  have hset : GSLit.B2Setting a Y S :=
    ⟨hYp.1.1, hYp.1.2.1, hYp.1.2.2, hSH, hSsyl, GSThmB.conclusionB2a_of_sylow hSsyl hall,
      hcentral⟩
  exact ⟨Y, GrSLit.gsWeakMaximalComponent_of_b2Setting hset, hYT, hYA⟩

theorem footeTopExclusion_of_gsMaximalSwap_of_rankIncrease (hsw : FooteGSMaximalSwapExclusion)
    (hRI : FooteRankIncrease) : Foote5.SolMax.FooteTopExclusion :=
  footeTopExclusion_of_gsMaximalSwap hsw (footeGSMaximalRepresentative_of_rankIncrease hRI)

theorem gsWeakCorr_reverse_of_gsIsoCorr {a b : G} {J K : Subgroup G}
    (h : UnbalancedGS.GSIsoCorr a J b K) : GrSLit.GSWeakCorr b K a J := by
  obtain ⟨hcorr, hKK, hsup⟩ := UnbalancedGS.gsIsoCorr_iff_sup.mp h
  have hTK : UnbalancedGS.gsFixedLayer J b ≤ K := hcorr.gsFixedLayer_le hKK
  have hW : GrSLit.GSWeakCorr a J b K := GrSLit.GSWeakCorr.of_gsCorr hcorr
  have hD := Foote5.SolMax.gsFixedLayer_common_component_of_gsWeakCorr hW
  have hKa : conjugate K a = K :=
    Subgroup.eq_of_le_of_card_ge (le_sup_right.trans hKK.le)
      (Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective).ge
  obtain ⟨ha, hb, hab, hJa, hJp, hKb, hKp, -, -, -⟩ := hW
  have haN : a ∈ normalizer (K : Set G) := UnbalancedLayer.mem_normalizer_of_conjugate_eq hKa
  have haD : a ∈ UnbalancedLayer.coreActionKernel (UnbalancedGS.gsFixedLayer J b) :=
    GSLit.mem_coreActionKernel_of_le_centralizer
      ((UnbalancedGS.gsFixedLayer_le_inf J b).trans (inf_le_left.trans hJa))
  have haK : a ∈ UnbalancedLayer.coreActionKernel K := mem_coreActionKernel_of_sup hTK hsup haN haD
  have hFix : UnbalancedGS.gsFixedLayer K a = UnbalancedGS.gsFixedLayer J b :=
    Foote5.SolMax.gsFixedLayer_eq_of_common_component ha ⟨hKb, hKp⟩ hab hKa haK hD hTK
  refine ⟨hb, ha, hab.symm, hKb, hKp, hJa, hJp, haN,
    (UnbalancedLayer.mem_coreActionKernel.mp haK).2, ?_⟩
  rw [hFix]
  exact (UnbalancedGS.gsFixedLayer_le_inf J b).trans (inf_le_left.trans le_sup_left)

theorem exists_isomorphicFamily_of_rankIncrease (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hRI : FooteRankIncrease) {t : G}
    {L : Subgroup G} (hmin : FooteMinimal G) (hce : FooteCounterexample G t L)
    (hsimp : IsSimpleGroup G) (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) {z s : G}
    {Y : Subgroup G} (hz : orderOf z = 2) (hs : orderOf s = 2) (hzs : z * s = s * z)
    (hYz : IsTwoComponentIn Y (centralizer ({z} : Set G))) (hY : GrSLit.GSWeakMaximalComponent Y)
    (hYT : Nonempty (Y ⧸ Open.fusionZStar Y ≃* L ⧸ Open.fusionZStar L))
    (hYs : conjugate Y s ≠ Y) :
    ∃ (𝓢 : Set (Subgroup G)) (z₀ s₀ : G) (Y₀ : Subgroup G),
      FooteMarked.IsomorphicFamily 𝓢 (L ⧸ Open.fusionZStar L) ∧ orderOf z₀ = 2 ∧
        orderOf s₀ = 2 ∧ z₀ * s₀ = s₀ * z₀ ∧ IsTwoComponentIn Y₀ (centralizer ({z₀} : Set G)) ∧
        Y₀ ∈ 𝓢 ∧ conjugate Y₀ s₀ ≠ Y₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let B : Set (G × Subgroup G × G) := {q | IsTwoComponentAt q.1 q.2.1 ∧
    GrSLit.GSWeakMaximalComponent q.2.1 ∧
    Nonempty (q.2.1 ⧸ Open.fusionZStar q.2.1 ≃* L ⧸ Open.fusionZStar L) ∧
    orderOf q.2.2 = 2 ∧ q.1 * q.2.2 = q.2.2 * q.1 ∧ conjugate q.2.1 q.2.2 ≠ q.2.1}
  obtain ⟨⟨z₀, Y₀, s₀⟩, ⟨hY₀z, hY₀, hY₀T, hs₀, hzs₀, hY₀s⟩, hmax₀⟩ := Set.exists_max_image B
    (fun q : G × Subgroup G × G => CFSG.pRank 2 ↥(centralizer ({q.1} : Set G) ⊓
      normalizer (q.2.1 : Set G) ⊓ UnbalancedLayer.coreActionKernel q.2.1))
    (Set.toFinite B) ⟨(z, Y, s), ⟨hz, hYz.1, hYz.2⟩, hY, hYT, hs, hzs, hYs⟩
  have hiso : ∀ (a : G) (J S : Subgroup G), IsTwoComponentAt a J →
      GrSLit.GSWeakMaximalComponent J →
      Nonempty (J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L) →
      CFSG.pRank 2 ↥(centralizer ({z₀} : Set G) ⊓ normalizer (Y₀ : Set G) ⊓
          UnbalancedLayer.coreActionKernel Y₀) ≤
        CFSG.pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓
          UnbalancedLayer.coreActionKernel J) →
      S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
      (∃ P : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
        (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) →
      ∀ b ∈ S ⊓ UnbalancedLayer.coreActionKernel J, orderOf b = 2 →
        ∃ K : Subgroup G, UnbalancedGS.GSIsoCorr a J b K := by
    intro a J S hJa hJ hJT hρ hSH hSsyl b hbP hb
    by_cases hba : b = a
    · obtain rfl := hba
      exact ⟨J, GSLit.gsIsoCorr_self hJa.1 hJa.2.1 hJa.2.2⟩
    by_contra hno
    have hbJ : b ∈ UnbalancedLayer.coreActionKernel J := (mem_inf.mp hbP).2
    have hab : a * b = b * a :=
      (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSH (mem_inf.mp hbP).1)).1).symm
    obtain ⟨K, hKb, -, hTK, -⟩ :=
      exists_footeStep footeLBalanceInput_holds hJa hb hab (Ne.symm hba) hbJ
    obtain ⟨hbN, hbO⟩ := UnbalancedLayer.mem_coreActionKernel.mp hbJ
    have hC : GrSLit.GSWeakCorr a J b K :=
      ⟨hJa.1, hb, hab, hJa.2.1, hJa.2.2, hKb.2.1, hKb.2.2, hbN, hbO, hTK⟩
    obtain ⟨e, K', -, -, hC', hK'a, hlt⟩ := hRI G t L hmin hce hsimp hrank2 a J S
      (footePointedMaximal_of_gsWeakMaximalComponent hJ hJa) hJT hSH hSsyl b K hb hbP hC
      (fun h => hno ⟨K, gsIsoCorr_of_gsWeakCorr hC h.1 h.2⟩)
    have hR1 : GrSLit.GSWeakReach J K' := Relation.ReflTransGen.single ⟨a, e, hC'⟩
    obtain ⟨eJK⟩ := hJ.2 K' hR1
    have hle := hmax₀ (e, K', a)
      ⟨⟨hC'.2.1, hC'.2.2.2.2.2.1, hC'.2.2.2.2.2.2.1⟩, hJ.of_weakReach hR1,
        ⟨eJK.symm.trans hJT.some⟩, hJa.1, hC'.2.2.1.symm, hK'a⟩
    rw [← centralizer_inf_normalizer_inf_coreActionKernel,
      ← centralizer_inf_normalizer_inf_coreActionKernel] at hlt
    exact absurd (hρ.trans_lt hlt) (not_lt.mpr hle)
  let R : Set (G × Subgroup G) := {p | IsTwoComponentAt p.1 p.2 ∧
    GrSLit.GSWeakMaximalComponent p.2 ∧
    Nonempty (p.2 ⧸ Open.fusionZStar p.2 ≃* L ⧸ Open.fusionZStar L) ∧ GrSLit.GSWeakReach p.2 Y₀}
  have hR₀ : (z₀, Y₀) ∈ R := ⟨hY₀z, hY₀, hY₀T, Relation.ReflTransGen.refl⟩
  obtain ⟨⟨a, J⟩, ⟨hJa, hJ, hJT, hJY⟩, hmax⟩ := Set.exists_max_image R
    (fun p : G × Subgroup G => toLex
      (CFSG.pRank 2 ↥(centralizer ({p.1} : Set G) ⊓ normalizer (p.2 : Set G) ⊓
        UnbalancedLayer.coreActionKernel p.2),
      2 ^ (Nat.card ↥(centralizer ({p.1} : Set G) ⊓ normalizer (p.2 : Set G))).factorization 2))
    (Set.toFinite R) ⟨(z₀, Y₀), hR₀⟩
  have hρ := (Prod.Lex.toLex_le_toLex'.mp (hmax _ hR₀)).1
  have hstep : ∀ (b : G) (K : Subgroup G), UnbalancedGS.GSIsoCorr a J b K → (b, K) ∈ R := by
    intro b K hK
    have hCK : GrSLit.GSWeakCorr a J b K :=
      GrSLit.GSWeakCorr.of_gsCorr (UnbalancedGS.gsIsoCorr_iff_sup.mp hK).1
    have hR1 : GrSLit.GSWeakReach J K := Relation.ReflTransGen.single ⟨a, b, hCK⟩
    obtain ⟨eJK⟩ := hJ.2 K hR1
    exact ⟨⟨hCK.2.1, hCK.2.2.2.2.2.1, hCK.2.2.2.2.2.2.1⟩, hJ.of_weakReach hR1,
      ⟨eJK.symm.trans hJT.some⟩,
      Relation.ReflTransGen.head ⟨b, a, gsWeakCorr_reverse_of_gsIsoCorr hK⟩ hJY⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
    inferInstance
  set S : Subgroup G := (P₀ : Subgroup _).map
    (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)).subtype with hSdef
  have hSH : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) := map_subtype_le _
  have hSsyl : ∃ P : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)) :=
    ⟨P₀, (comap_map_eq_self_of_injective
      (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)).subtype_injective _).symm⟩
  have hcentral : ∀ (b : G) (K : Subgroup G), orderOf b = 2 →
      b ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
      (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
      UnbalancedGS.GSIsoCorr a J b K → b ∈ S → (∀ x ∈ S, x * b = b * x) →
      S ≤ centralizer ({b} : Set G) ⊓ normalizer (K : Set G) ∧
        ∃ P : Sylow 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (K : Set G)),
          (P : Subgroup _) = S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (K : Set G)) := by
    intro b K _ _ _ hK _ hbZ
    have hSb : S ≤ centralizer ({b} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (hbZ x hx)
    obtain ⟨-, -, -, -, -, -, -, -, hgrow⟩ :=
      UnbalancedLayer.isomorphic_correspondence_sylow_growth hK rfl rfl rfl rfl
    obtain ⟨hSHL, hρ', -, hstrict, -⟩ := hgrow S hSH hSsyl hSb
    refine ⟨hSHL, ?_⟩
    by_contra hns
    obtain ⟨hle1, hle2⟩ := Prod.Lex.toLex_le_toLex'.mp (hmax _ (hstep b K hK))
    exact absurd (hle2 (le_antisymm hle1 hρ')) (not_le.mpr (hstrict hns))
  have hset : GSLit.B2Setting a J S :=
    ⟨hJa.1, hJa.2.1, hJa.2.2, hSH, hSsyl,
      GSThmB.conclusionB2a_of_sylow hSsyl (hiso a J S hJa hJ hJT hρ hSH hSsyl), hcentral⟩
  have hJF : J ∈ footeFamilyOf L :=
    mem_footeFamilyOf_of_gsWeakMaximalComponent hJa.1 ⟨hJa.2.1, hJa.2.2⟩ hJ hJT
  obtain ⟨-, hJO⟩ := isSimpleGroup_quotient_of_mem_footeFamilyOf hGA hGC hSA hce.1.2.2.2.2.1
    hrank2 hJa hJF
  exact ⟨GrSLit.gsForwardFamily J, z₀, s₀, Y₀,
    GrSLit.isomorphicFamily_forwardFamily_of_B2Setting hset hJO, hY₀z.1, hs₀, hzs₀,
    ⟨hY₀z.2.1, hY₀z.2.2⟩, ⟨Y₀, hJY, 1, (UnbalancedLayer.conjugate_one Y₀).symm⟩, hY₀s⟩

@[expose] def FooteIsomorphicFamilySwapExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → IsSimpleGroup G →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    ∀ 𝓢 : Set (Subgroup G), FooteMarked.IsomorphicFamily 𝓢 (L ⧸ Open.fusionZStar L) →
    ∀ (z s : G) (Y : Subgroup G), orderOf z = 2 → orderOf s = 2 → z * s = s * z →
      IsTwoComponentIn Y (centralizer ({z} : Set G)) → Y ∈ 𝓢 → conjugate Y s ≠ Y → False

theorem footeGSMaximalSwapExclusion_of_rankIncrease (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hRI : FooteRankIncrease)
    (hIF : FooteIsomorphicFamilySwapExclusion) : FooteGSMaximalSwapExclusion := by
  intro G _ _ t L hmin hce hsimp hrank2 z s Y hz hs hzs hYz hY hYT hYs
  obtain ⟨𝓢, z₀, s₀, Y₀, hfam, hz₀, hs₀, hzs₀, hY₀z, hY₀, hY₀s⟩ :=
    exists_isomorphicFamily_of_rankIncrease hGA hGC hSA hRI hmin hce hsimp hrank2 hz hs hzs hYz
      hY hYT hYs
  exact hIF G t L hmin hce hsimp hrank2 𝓢 hfam z₀ s₀ Y₀ hz₀ hs₀ hzs₀ hY₀z hY₀ hY₀s

theorem footeTopExclusion_of_rankIncrease_of_isomorphicFamilySwap
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hRI : FooteRankIncrease)
    (hIF : FooteIsomorphicFamilySwapExclusion) : Foote5.SolMax.FooteTopExclusion :=
  footeTopExclusion_of_gsMaximalSwap_of_rankIncrease
    (footeGSMaximalSwapExclusion_of_rankIncrease hGA hGC hSA hRI hIF) hRI

end CFSG.ComponentClassification.FooteLit
