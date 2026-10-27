module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieListInvolveWShape
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorusFamilies
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Ident
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Norm

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def KFactOneLieAutRankSq : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      ∀ E : Subgroup (MulAut K), IsElemAbelian p E →
        Nat.card E < Nat.card (T : Subgroup K) ^ 2

theorem kFactOneLieAutRankSq_of (hId : KFactOneLieIdent) (hKU2 : KFactUnitarySylowStructure)
    (hKU9 : KFactUnitaryAutElemRank) (hKR6 : KFactReeAutElemRank) (hKR8 : KFactReeOrder) :
    KFactOneLieAutRankSq := by
  intro K _ _ hs hnab hcat p hp hp2 T hTnc hΓ hbig E hE
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hfam, he⟩ := hId K hs hnab hcat p hp hp2 T hTnc hΓ hbig
  rcases hfam with ⟨n, hn3, hdn⟩ | ⟨hdU, hn2⟩ | hdR
  ·
    obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdn
    obtain ⟨e⟩ := he
    have hEc := (oneLieTorusFacts_of_psl2GF hKU2 hp2 hn3 (e.trans f) T).autRank E hE
    simp only [↓reduceIte] at hEc
    have hfs : Function.Surjective ((e.trans f : K ≃* PSL2GF p n) : K →* PSL2GF p n) :=
      (e.trans f).surjective
    have hTc : Nat.card (T : Subgroup K) = p ^ n := by
      rw [← (psl2GF_sylow p n (by omega) (T.mapSurjective hfs)).2, Sylow.coe_mapSurjective hfs T,
        Subgroup.card_map_of_injective (show Function.Injective
          ((e.trans f : K ≃* PSL2GF p n) : K →* PSL2GF p n) from (e.trans f).injective)]
    rw [hTc, ← pow_mul]
    exact hEc.trans_lt (Nat.pow_lt_pow_right hp.one_lt (by omega))
  ·
    have hEc := hKU9 K p d hdU he E hE
    obtain ⟨hTc, -⟩ := hKU2 K p d hp2 hdU he T
    rw [hTc, ← pow_mul]
    exact hEc.trans_lt (Nat.pow_lt_pow_right hp.one_lt (by omega))
  ·
    obtain ⟨rfl, m, hm⟩ := hdR
    have ha := IsReeGTwoIndex.three_le_fieldExponent (p := 3) ⟨rfl, m, hm⟩
    have hEc := hKR6 K d ⟨rfl, m, hm⟩ he E hE
    have hR := hKR8 K d ⟨rfl, m, hm⟩ he
    have hTd : 3 ^ (3 * d.1.fieldExponent) ∣ Nat.card (T : Subgroup K) :=
      T.pow_dvd_card_of_pow_dvd_card (by
        rw [hR, pow_mul']
        exact (dvd_mul_right _ _).mul_right _)
    have hTle := Nat.le_of_dvd Nat.card_pos hTd
    calc Nat.card E ≤ 3 ^ (2 * d.1.fieldExponent) := hEc
      _ < (3 ^ (3 * d.1.fieldExponent)) ^ 2 := by
        rw [← pow_mul]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ Nat.card (T : Subgroup K) ^ 2 := Nat.pow_le_pow_left hTle 2

namespace D1OneLieCompetitorData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {R₁ : Subgroup G} {P' : Sylow p G}
  {H₁ S : Subgroup G}


theorem isComponentOf_map_nclIn (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (hSch : KFactCatalogSchreier) (hCO : KFactOneLieCenterOver) (hAR : KFactOneLieAutRankSq)
    (hK : KFactOneLie) (hTor : KFactOneLieTorus) (hβ : KFactBeta) (hα : KFactAlphaW)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hKl : KFactKlingenSpFour)
    (hin : KFactChevTwoInnerGen) (hout : KFactChevTwoOuterGen)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hSF : SporCaseThreeKFacts) (hLIW : KFactOneLieListInvolveW)
    (hRC : KFactRankOneCoreProper) (hKU1 : KFactUnitarySchur) (hKR1 : KFactReeSchur)
    (hKU2 : KFactUnitarySylowStructure) (hKU3 : KFactUnitarySylowCenterTorus)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K) :
    IsComponentOf (((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) ⊤ := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  have hkz : D1OneLieKZeroData p P M H R Rbar K P' H₁ S :=
    ⟨hc.data, hc.escape, hc.nclIn_le, hc.liftX_le.trans hc.le_S⟩
  obtain ⟨Rb₁, L, T₁, h⟩ := hkz.exists_comp_of_listInvolveW hTor hSch hβ hα hP1L hP1A hKl hin
    hout hOutS hSF hLIW hRC hKU1 hKR1 hc.not_hasPrimeConstraint
  have : L.Normal := h.normal
  obtain ⟨n, e, hTF⟩ := h.exists_torusFacts hTor
  obtain ⟨-, h3₁⟩ := h.toPhaseThree hK hTF
  have hXJ : ((d1LiftX p H R K).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
    Subgroup.map_mono (Subgroup.comap_mono (le_nclIn (d1LiftX_le_H p H R K)))
  have hZT := hkz.centerOf_le_d1MapPCore hK h84 hD2 hY hWK h3₁ Rb₁ h.noncyclic h.borel_le
    h.not_le h.center T₁ h.sylow (h.oneLieFacts hK) hTF (hXJ.trans h.le)
  have hW := hkz.d1MapPCore_le_map_liftX hK h84 hD2 hWK h3₁
  rcases h.eq_or_unitary hCO ((hZT.trans hW).trans hXJ) with hJL | ⟨hU, hcardZ⟩
  · rw [hJL]
    exact h.comp
  exfalso
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  have hR₁H : R₁ ≤ H := hc.le_R.trans hd.cfg.ext.le_H
  set R₁b := (R₁.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))
    with hR₁b
  set A : Subgroup (MulAut K) := R₁b.map (MulAut.conjNormal (H := K)) with hA
  have hR₁bker : R₁b ⊓ (MulAut.conjNormal (H := K)).ker = ⊥ := by
    rw [ker_conjNormal_eq_centralizer, eq_bot_iff]
    rintro _ ⟨⟨r, hr, rfl⟩, hrC⟩
    have hmem : (r : G) ∈ R₁ ⊓ d1PlusCore p H K := ⟨Subgroup.mem_subgroupOf.mp hr, ⟨r, hrC, rfl⟩⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot, show r = 1 from Subtype.ext hmem, map_one]
  have hrkA : Open.pRank p R₁ ≤ Open.pRank p A := by
    have h1 := pRank_le_pRank_inf_ker_add_pRank_map hp (MulAut.conjNormal (H := K)) R₁b
    rw [hR₁bker, pRank_bot_eq_zero hp, zero_add] at h1
    have h2 : Open.pRank p R₁b = Open.pRank p R₁ := by
      rw [hR₁b, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
        Subgroup.map_subgroupOf_eq_of_le hR₁H]
    rw [← h2]
    exact h1
  have hrkS : Open.pRank p ((S.subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) = Open.pRank p S := by
    rw [pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      Subgroup.map_subgroupOf_eq_of_le hc.escape.le_H]
  have hrk : Open.pRank p (⊤ : Subgroup L) ≤ Open.pRank p A := by
    rw [← pRank_sylow_eq_globalRank p hp T₁,
      ← pRank_map_of_injective p hp L.subtype L.subtype_injective, h.sylow]
    calc Open.pRank p ((Rb₁ : Subgroup _) ⊓ L) ≤ Open.pRank p (Rb₁ : Subgroup _) :=
          pRank_mono p hp inf_le_left
      _ = Open.pRank p S := by rw [h.rbar, hrkS]
      _ ≤ Open.pRank p R₁ := hc.pRank_le
      _ ≤ Open.pRank p A := hrkA
  obtain ⟨d, hdU, hLd⟩ := hU
  obtain ⟨-, -, -, E, -, hE, hEcard⟩ := hKU2 L p d hc.escape.ne_two hdU hLd T₁
  obtain ⟨ψZ, hψZinj, hψZrange, -⟩ := hKU3 L p d hdU hLd T₁
  obtain ⟨q, -, -, hfe, hq1⟩ := hdU.exists_eq
  have hfe0 : d.1.fieldExponent ≠ 0 := by omega
  have hZcard : Nat.card ((T₁ : Subgroup L) ⊓
      Subgroup.centralizer ((T₁ : Subgroup L) : Set L) : Subgroup L) =
      p ^ d.1.fieldExponent := by
    rw [← hψZrange, ← Nat.card_congr (MonoidHom.ofInjective hψZinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (GaloisField p
        d.1.fieldExponent) ≃ _), GaloisField.card p _ hfe0]
  have h2fe : 2 * d.1.fieldExponent ≤ Open.pRank p (⊤ : Subgroup L) :=
    le_csSup (pRank_bddAbove p hp _) ⟨E, le_top, hE, hEcard⟩
  obtain ⟨EA, -, hEA, hEAcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  obtain ⟨hKs, hKnab⟩ := hd.isSimpleGroup
  obtain ⟨T', -, hKcat', hTnc', hΓ', hTX'⟩ := hd.exists_kFactHyps
  have hlt := hAR K hKs hKnab hKcat' p hp hc.escape.ne_two T' hTnc' hΓ' hd.big EA hEA
  rw [hTX', ← hcardZ, hZcard, hEAcard, ← pow_mul] at hlt
  have h1 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  omega

end D1OneLieCompetitorData

theorem d1OneLieCompetitorComp_of (hSch : KFactCatalogSchreier)
    (hCO : KFactOneLieCenterOver) (hAR : KFactOneLieAutRankSq) (hK : KFactOneLie)
    (hTor : KFactOneLieTorus) (hβ : KFactBeta) (hα : KFactAlphaW) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hKl : KFactKlingenSpFour) (hin : KFactChevTwoInnerGen)
    (hout : KFactChevTwoOuterGen)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hSF : SporCaseThreeKFacts) (hLIW : KFactOneLieListInvolveW)
    (hRC : KFactRankOneCoreProper) (hKU1 : KFactUnitarySchur) (hKR1 : KFactReeSchur)
    (hKU2 : KFactUnitarySylowStructure) (hKU3 : KFactUnitarySylowCenterTorus)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) : D1OneLieCompetitorComp :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hY hWK =>
    hc.isComponentOf_map_nclIn hSch hCO hAR hK hTor hβ hα hP1L hP1A hKl hin hout hOutS hSF hLIW
      hRC hKU1 hKR1 hKU2 hKU3 h84 hD2 hY hWK

end CFSG.AGLEmbedding
