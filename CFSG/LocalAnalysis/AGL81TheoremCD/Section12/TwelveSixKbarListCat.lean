module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.Assembly.OpenBridges

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.AGL81I.Section3 (KGroupLowRank24_12 Catalogue24_12)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

namespace KbarList

theorem map_primeComplementCore_le (p : ℕ) (H : Subgroup G) :
    (primeComplementCore (G := ↥H) p).map H.subtype ≤ relPPrimeCore p H := by
  refine le_sSup ⟨map_subtype_le _, ?_, ?_⟩
  · rw [← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  · rw [← Nat.card_congr (equivMapOfInjective _ _ H.subtype_injective).toEquiv]
    exact primeComplementCore_coprime (G := ↥H) p

theorem pCore_two_le_primeComplementCore (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G) :
    CFSG.pCore 2 ↥H ≤ primeComplementCore (G := ↥H) p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine normal_coprime_le_primeComplementCore p _ inferInstance ?_
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem pCore_two_le_ker (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G} (hKH : K ≤ H)
    (hKn : (K.subgroupOf H).Normal) :
    CFSG.pCore 2 ↥K ≤
      ((QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp (inclusion hKH)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  apply pCore_two_le_primeComplementCore hp hp2 H
  have h1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := pCoreOf_le_of_normal_subgroupOf 2 K H hKH hKn h1
  have hyx' : y = inclusion hKH x := Subtype.ext hyx
  rw [← hyx']
  exact hy

end KbarList

theorem TwelveSixKbarHyp.kStar_catalogue (hcat : Catalogue24_12)
    (hB : CFSG.Assembly.CatalogAgreeOn CFSG.Assembly.InCatalog CFSG.Blueprint.Catalog)
    (hyp : TwelveSixKbarHyp G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H) :
    KGroupLowRank24_12 p ↥(kStar p M H) ∧
      CFSG.Open.pRank p (⊤ : Subgroup ↥(kStar p M H)) ≤ 3 ∧
      Nonempty (↥(kStar p M H) ⧸ center ↥(kStar p M H) ≃* kbarQuot p M H) := by
  obtain ⟨hc, -, -, hL, -, -, hKH⟩ := hyp
  have hp : p.Prime := hc.ctx.p_prime
  have hp2 : p ≠ 2 := hc.ctx.p_odd
  have : Fact p.Prime := ⟨hp⟩
  have hKleH : kSub p M H ≤ H := Section14.kSub_le p M H
  set ι : ↥(kSub p M H) →* StarGroup p H :=
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).comp (inclusion hKleH) with hι
  set f : modTwoCore (kSub p M H) →* StarGroup p H :=
    QuotientGroup.lift (CFSG.pCore 2 ↥(kSub p M H)) ι
      (KbarList.pCore_two_le_ker hp hp2 hKleH hKH) with hf
  have hfrange : f.range = kStar p M H := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨inclusion hKleH x, by simp [mem_subgroupOf], rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨QuotientGroup.mk ⟨y, hy⟩, rfl⟩
  have hOM : (primeComplementCore (G := ↥H) p).map H.subtype ≤ M :=
    (KbarList.map_primeComplementCore_le p H).trans (relPPrimeCore_le_M_of_twelveCtx hc.ctx)
  have hKstarM : ¬ kStar p M H ≤ starImg p H M := by
    intro hle
    apply Section14.not_kSub_le_of_not_pLayerIn_le hL
    intro k hk
    have hmem : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨k, hKleH hk⟩ :
        StarGroup p H) ∈ starImg p H M :=
      hle ⟨⟨k, hKleH hk⟩, by simpa [mem_subgroupOf] using hk, rfl⟩
    obtain ⟨m, hm, hmk⟩ := hmem
    have h1 : m⁻¹ * ⟨k, hKleH hk⟩ ∈ primeComplementCore (G := ↥H) p := QuotientGroup.eq.1 hmk
    have h2 : ((m⁻¹ * ⟨k, hKleH hk⟩ : ↥H) : G) ∈ M := hOM ⟨_, h1, rfl⟩
    have h3 : (m : G) ∈ M := hm
    have hk' : k = (m : G) * ((m⁻¹ * ⟨k, hKleH hk⟩ : ↥H) : G) := by simp
    rw [hk']
    exact M.mul_mem h3 h2
  have hKs_ne : kStar p M H ≠ ⊥ := fun hbot => hKstarM (hbot ▸ bot_le)
  have hq : CFSG.IsQuasisimple ↥(kStar p M H) := by
    rcases ComponentInitial.quasisimple_homomorphic_images hK.2.2.1 f with h | h
    · exact absurd (hfrange ▸ h) hKs_ne
    · exact hfrange ▸ h
  have hKn : (kStar p M H).Normal := Section15.starImg_normal hKH
  have hcore : CFSG.pPrimeCore p ↥(kStar p M H) = ⊥ := by
    have h1 := CFSG.GH74.GLS.pPrimeCoreOf_le_of_subnormal p hKn.isSubnormal
    rw [Section15.pPrimeCore_starGroup hp, le_bot_iff] at h1
    exact (map_eq_bot_iff_of_injective _ (subtype_injective _)).1 h1
  have hKG : CFSG.SectionRank.IsKGroupCat ↥(kStar p M H) := by
    have hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G :=
      ((CFSG.Assembly.kProper_inCatalog_iff_isKProper G).mpr
        hc.ctx.cstar.kProper).of_catalogAgree hB
    have hH : CFSG.SectionRank.IsKGroupCat ↥H :=
      CFSG.KCore.KProperNonab.kGroupAllSimple CFSG.SectionRank.catalog_isoInvariant
        CFSG.SectionRank.catalog_containsAbelianSimple hKP H hc.ctx.H_ne_top
    exact (hH.quotient (primeComplementCore (G := ↥H) p)).subgroup _
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  have hEH : E ≤ H := hEQ.trans hc.ctx.Q_le_H
  have hEp : IsPGroup p E := hE.isPGroup
  have hEs : IsElemAbelian p (starImg p H E) :=
    (Section15.isElemAbelian_starImg_iff hp hEH hEp).2 hE
  have hEsc : Nat.card (starImg p H E) = p ^ 2 := by
    rw [← Nat.card_congr (Section15.starImgMulEquiv hp hEH hEp).toEquiv, hEc]
  have hrkX : CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) ≤ 3 := by
    have h := Section15.pRank_starImg_eq_pRank_inf (H := H) hp ⊤
    have htop : starImg p H (⊤ : Subgroup G) = ⊤ := by
      rw [starImg, top_subgroupOf]
      exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [htop, inf_top_eq] at h
    rw [h]
    exact hc.pRank_le_three
  have hrk : CFSG.Open.pRank p (kStar p M H ⊔ starImg p H E) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hrkX
  have hα : ¬ kStar p M H ≤ gammaOver 1 p (starImg p H E) (kStar p M H) := by
    intro hle
    apply hKstarM
    have hND : ∀ D : Subgroup G, D ≤ E → 1 ≤ CFSG.Open.pRank p D →
        normalizer (D : Set G) ≤ CFSG.Open.rankThreeGamma 1 p E := by
      intro D hDE h1D
      unfold CFSG.Open.rankThreeGamma CFSG.Open.GLBCore
      exact le_sSup ⟨D, hDE, h1D, rfl⟩
    have hΓs : CFSG.Open.rankThreeGamma 1 p (starImg p H E) ≤ starImg p H M :=
      Section15.rankThreeGamma_starImg_le hp hEH hEp fun D hDE h1D =>
        inf_le_left.trans ((hND D hDE h1D).trans hΓ)
    refine hle.trans (le_trans ?_ hΓs)
    refine iSup_le fun F => iSup_le fun hF => iSup_le fun h1F => inf_le_left.trans ?_
    unfold CFSG.Open.rankThreeGamma CFSG.Open.GLBCore
    exact le_sSup ⟨F, hF, h1F, rfl⟩
  have hcatK := hcat (StarGroup p H) (kStar p M H) (starImg p H E) p hp hp2 hq hcore hKG hKn
    hEs hEsc hrk hα
  have hrkK : CFSG.Open.pRank p (⊤ : Subgroup ↥(kStar p M H)) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hrkX
  have hiso : Nonempty (↥(kStar p M H) ⧸ center ↥(kStar p M H) ≃* kbarQuot p M H) := by
    have hfmem : ∀ x, f x ∈ kStar p M H := fun x => hfrange ▸ ⟨x, rfl⟩
    set f' : modTwoCore (kSub p M H) →* ↥(kStar p M H) := f.codRestrict _ hfmem with hf'
    have hf'surj : Function.Surjective f' := by
      rintro ⟨z, hz⟩
      rw [← hfrange] at hz
      obtain ⟨x, rfl⟩ := hz
      exact ⟨x, rfl⟩
    have hker : f'.ker ≤ center (modTwoCore (kSub p M H)) := by
      rcases ComponentInitial.quasisimple_normal_subgroups hK.2.2.1 f'.normal_ker with h | h
      · exfalso
        apply hKs_ne
        rw [← hfrange, eq_bot_iff]
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ f'.ker := h ▸ mem_top x
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
        exact mem_bot.2 this
      · exact h
    obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hK.2.2.1.1 f' hf'surj hker
    exact ⟨e.symm⟩
  exact ⟨hcatK, hrkK, hiso⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
