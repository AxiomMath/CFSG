module

public import CFSG.LocalAnalysis.RankFourTheoremC.FullCoreRank4
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankFourTheoremC.PRankCube
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedCentral
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXWeakCoreSaturation
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ReducedComponentStructure

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open CFSG.AGLEmbedding
  CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_pPrime_normalized (hS : D1Global G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {K : Subgroup G}
    (hK : ¬ p ∣ Nat.card K) (hPK : (P : Subgroup G) ≤ normalizer (K : Set G)) : K ≤ M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have h4 := four_le_pRank_sylow (mem_betaFour_of_mem_sigmaA hS.rank hp) P
  obtain ⟨E, hEP, hE, hEc⟩ :=
    exists_isElemAbelian_card_pow_three hprime (H := (P : Subgroup G)) (by omega)
  have hrank : 3 ≤ CFSG.Assembly.pRank p (⊤ : Subgroup G) := by
    have := pRank_mono p hprime.one_lt (le_top : (P : Subgroup G) ≤ ⊤)
    change 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G)
    omega
  obtain ⟨hPW, -, -, -, -, -, -, habsorb, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.weak_core_sylow_saturation_and_locality hprime hodd hrank P
      (W := CFSG.Assembly.LargeEvenWeakCore p (P : Subgroup G)) rfl
  have hKW := habsorb E K 3 (hEP.trans hPW) hE hEc le_rfl hK (hEP.trans hPK)
  exact hKW.trans hM.2

theorem center_map_eq_bot {X : Type*} [Group X] {K : Subgroup X} (e : X ≃* X)
    (hK : center K = ⊥) : center (K.map e.toMonoidHom) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨c, hcmem⟩ hc
  obtain ⟨k, hk, rfl⟩ := hcmem
  have hkc : (⟨k, hk⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro g
    have h := mem_center_iff.1 hc ⟨e g, Subgroup.mem_map_of_mem _ g.2⟩
    have h' : e g * e k = e k * e g := congrArg Subtype.val h
    apply Subtype.ext
    apply e.injective
    simpa [map_mul] using h'
  rw [hK, mem_bot] at hkc
  have hk1 : k = 1 := congrArg Subtype.val hkc
  subst hk1
  exact mem_bot.2 (Subtype.ext (map_one e))

theorem center_eq_bot_of_pCore_eq_bot {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hcore : primeComplementCore (G := X) p = ⊥) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hpc : CFSG.pCore p K = ⊥) : center K = ⊥ := by
  have hcoreK := cfsg_subnormal_primeComplementCore_eq_bot p K hK.2.1 hcore
  have hZ := trivial_primeComplementCore_center_le_pCore p hp hcoreK
  exact le_bot_iff.1 (hZ.trans hpc.le)

theorem dvd_card_of_isComponentOf {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hcore : primeComplementCore (G := X) p = ⊥) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    p ∣ Nat.card K := by
  by_contra hnd
  have hcoreK := cfsg_subnormal_primeComplementCore_eq_bot p K hK.2.1 hcore
  have hle := normal_coprime_le_primeComplementCore p (⊤ : Subgroup K) inferInstance
    (by rw [Subgroup.card_top]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  rw [hcoreK] at hle
  have hsimple := hK.2.2.2
  have : Nontrivial (K ⧸ center K) := hsimple.toNontrivial
  have : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne K
  exact hab ((mem_bot.1 (hle (mem_top a))).trans (mem_bot.1 (hle (mem_top b))).symm)

theorem layerLemma_of_componentPCoreTrivial (hS : D1Global G)
    (h243 : GL83ComponentPCoreTrivial) : GL83LayerLemma G := by
  intro p hp P M D hext hPD z hzD hz1 hzc hzp
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hM := hext.obstruction.1
  have hzH : z ∈ normalizer ((zpowers z : Subgroup G) : Set G) := le_normalizer (mem_zpowers z)
  set H : Subgroup G := normalizer ((zpowers z : Subgroup G) : Set G) with hHdef
  have hPH : (P : Subgroup G) ≤ H := le_normalizer_zpowers_of_le_centralizer hzc
  have hHtop : H ≠ ⊤ := normalizer_zpowers_ne_top hS hz1
  have hzn : (zpowers (⟨z, hzH⟩ : H)).Normal := normal_zpowers_subtype_mk z hzH
  set O : Subgroup H := primeComplementCore (G := H) p with hOdef
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hOM : O.map H.subtype ≤ M := by
    refine le_of_pPrime_normalized hS hp hM ?_
      (hPH.trans (CFSG.ABGTheoremB.le_normalizer_map_subtype H O))
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hprime).1 hO
  set X := H ⧸ O with hXdef
  set π : H →* X := QuotientGroup.mk' O with hπ
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections X :=
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H hHtop).quotient O
  have hcore : primeComplementCore (G := X) p = ⊥ := primeComplementCore_quotient_eq_bot p
  set Pbar : Sylow p X := (P.subtype hPH).mapSurjective (QuotientGroup.mk'_surjective O)
    with hPbardef
  have hPbar : (Pbar : Subgroup X) = ((P : Subgroup G).subgroupOf H).map π := by
    rw [hPbardef, Sylow.coe_mapSurjective, Sylow.coe_subtype]
  have hrankPbar : 3 ≤ CFSG.Open.pRank p (Pbar : Subgroup X) := by
    have h4 := four_le_pRank_sylow (mem_betaFour_of_mem_sigmaA hS.rank hp) P
    rw [hPbar, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hprime O hO,
      map_subgroupOf_eq_of_le hPH]
    omega
  set T : Subgroup X := ((H ⊓ M).subgroupOf H).map π with hTdef
  have hOT : O ≤ (H ⊓ M).subgroupOf H := fun x hx =>
    mem_subgroupOf.2 ⟨x.2, hOM ⟨x, hx, rfl⟩⟩
  have hWT : GLBWeakCore p (Pbar : Subgroup X) ≤ T := by
    rw [hPbar]
    exact weakCore_map_le_map_inf_of_coprime hprime P hM.2 le_rfl hPH O hO hOT
  by_contra hE
  obtain ⟨K₀, hK₀, hK₀T⟩ : ∃ K₀ : Subgroup X, IsComponentOf K₀ ⊤ ∧ ¬ K₀ ≤ T := by
    by_contra hno
    push Not at hno
    apply hE
    rintro g ⟨h, hh, rfl⟩
    obtain ⟨t, ht, hth⟩ := (sSup_le fun K hK => hno K hK : rankThreeLayer (⊤ : Subgroup X) ≤ T) hh
    have hmem : t⁻¹ * h ∈ O := QuotientGroup.eq.1 hth
    have htM : (t : G) ∈ M := (mem_subgroupOf.1 ht).2
    have hoM : (((t⁻¹ * h : H)) : G) ∈ M := hOM ⟨_, hmem, rfl⟩
    have : ((t * (t⁻¹ * h) : H) : G) ∈ M := M.mul_mem htM hoM
    simpa using this
  have hK₀pc : CFSG.pCore p K₀ = ⊥ :=
    h243 X hcat p Pbar K₀ hprime hodd hrankPbar hK₀ (fun h => hK₀T (h.trans hWT))
  set F : Set (Subgroup X) := {K | IsComponentOf K ⊤ ∧ center K = ⊥} with hF
  set Y : Subgroup X := sSup F with hY
  have hK₀F : K₀ ∈ F := ⟨hK₀, center_eq_bot_of_pCore_eq_bot hprime hcore hK₀ hK₀pc⟩
  have hK₀Y : K₀ ≤ Y := le_sSup hK₀F
  have hFconj : ∀ x : X, ∀ K ∈ F, K.map (MulAut.conj x).toMonoidHom ∈ F := by
    rintro x K ⟨hKc, hKz⟩
    exact ⟨(CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj x) K).mpr hKc,
      center_map_eq_bot _ hKz⟩
  have hYn : Y.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : Y.map (MulAut.conj g).toMonoidHom ≤ Y := by
      rw [map_le_iff_le_comap]
      refine sSup_le fun K hK => ?_
      rw [← map_le_iff_le_comap]
      exact le_sSup (hFconj g K hK)
    simpa using h1 ⟨n, hn, rfl⟩
  have hdvdY : p ∣ Nat.card Y :=
    (dvd_card_of_isComponentOf hprime hcore hK₀).trans (card_dvd_of_le hK₀Y)
  set E₁ : Subgroup G := (Y.comap π).map H.subtype with hE₁
  have hE₁H : E₁ ≤ H := map_subtype_le _
  have hHE₁ : H ≤ normalizer (E₁ : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype H _
  have hinf := inf_comap_ne_bot_of_dvd_card O (P.subtype hPH) hdvdY
  have hSE₁ : (P : Subgroup G) ⊓ E₁ ≠ ⊥ := by
    intro hbot
    apply hinf
    rw [eq_bot_iff]
    rintro t ⟨htP, htE⟩
    have htP' : (t : G) ∈ (P : Subgroup G) := by
      rw [Sylow.coe_subtype] at htP
      exact htP
    have : (t : G) ∈ (P : Subgroup G) ⊓ E₁ := ⟨htP', t, htE, rfl⟩
    rw [hbot, mem_bot] at this
    exact mem_bot.2 (Subtype.ext this)
  have hzE₁ : z ∈ E₁ := hext.mem_of_inf_ne_bot hprime hodd hPD (hPH.trans hHE₁) hSE₁ hzD hz1 hzc hzp
  set zH : H := ⟨z, hzH⟩ with hzHdef
  have hzbY : π zH ∈ Y := by
    obtain ⟨h, hh, hhz⟩ := hzE₁
    have : h = zH := Subtype.ext hhz
    rw [this] at hh
    exact hh
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hzHord : orderOf zH = p := by rw [← Subgroup.orderOf_coe]; exact hzord
  have hzbord : orderOf (π zH) = p := orderOf_mk_of_coprime hprime O hO hzHord
  have hzb1 : π zH ≠ 1 := fun h => by
    rw [h, orderOf_one] at hzbord
    exact hprime.one_lt.ne hzbord
  have hzbn : (zpowers (π zH)).Normal := by
    rw [← MonoidHom.map_zpowers]
    exact hzn.map π (QuotientGroup.mk'_surjective O)
  have hfin : F.Finite := Set.toFinite _
  have hYfin : Y = ⨆ K ∈ hfin.toFinset, K :=
    le_antisymm (sSup_le fun K hK => le_iSup₂_of_le K (hfin.mem_toFinset.2 hK) le_rfl)
      (iSup₂_le fun K hK => le_sSup (hfin.mem_toFinset.1 hK))
  exact hzb1 (eq_one_of_mem_iSup_components hfin.toFinset
    (fun K hK => (hfin.mem_toFinset.1 hK).1) (fun K hK => (hfin.mem_toFinset.1 hK).2) (π zH)
    (hYfin ▸ hzbY) fun K hK x hx => by
      have hKl : K ≤ rankThreeLayer (⊤ : Subgroup X) := le_sSup (hfin.mem_toFinset.1 hK).1
      exact commute_of_mem_layer hzbn (hKl hx))

theorem layerLemmaRank4_of_componentPCoreTrivial (h243 : GL83ComponentPCoreTrivial) :
    LayerLemmaRank4 :=
  fun _ _ _ _ hnonab hK hchar he hpre =>
    layerLemma_of_componentPCoreTrivial ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩ h243

theorem fullCoreRank4_of_componentPCoreTrivial (hD1 : D1Rank4)
    (hpend : ∀ (G : Type) [Group G] [Finite G], FischerRankFourPending G)
    (h243 : GL83ComponentPCoreTrivial) (h13 : InvariantTwoSylowOfD1Rank4)
    (hX : RelativePairExclusionOfD1Rank4) : FullCoreRank4 :=
  fullCoreRank4_of_pending hD1 hpend (layerLemmaRank4_of_componentPCoreTrivial h243) h13 hX

end CFSG.LocalAnalysis.RankFourTheoremC
