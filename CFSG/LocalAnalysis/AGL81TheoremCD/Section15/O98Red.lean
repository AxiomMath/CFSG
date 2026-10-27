module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O97Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Quot
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSevenA
import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRNoX
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec4.T444.Statement
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

private theorem exists_elemAbelian_nine {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQc : ¬ IsCyclic ↥Q) : ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B, hB, hBcard⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (p := 3) (by decide : Odd 3) hQ hQc
  refine ⟨B.map Q.subtype, Subgroup.map_subtype_le B, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map
      ((CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 3) (E := B)).mpr hB) Q.subtype
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hBcard]
    norm_num

private theorem three_not_mem_sigmaA {M Q : Subgroup G} (h3 : 3 ∉ S15.sigmaM G M) (hQM : Q ≤ M)
    (hQ : IsPGroup 3 Q) (hQc : ¬ IsCyclic ↥Q) : 3 ∉ rankThreeSigmaA G := by
  intro h3A
  apply h3
  refine ⟨h3A, ?_⟩
  obtain ⟨E, hEQ, hE, hEcard⟩ := exists_elemAbelian_nine hQ hQc
  have hle := CFSG.SectionRank.le_pRank (p := 3) (by norm_num : 1 < 3)
    (hEQ.trans hQM) hE (show Nat.card E = 3 ^ 2 by rw [hEcard]; norm_num)
  simpa using hle

private theorem three_not_mem_sigmaSet {M : Subgroup G} (h3 : 3 ∉ S15.sigmaM G M) :
    3 ∉ CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet G M := by
  intro h
  exact h3 (by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h)

private theorem centralizer_singleton_ne_top (hC : CStarGen G) {x : G}
    (hx : orderOf x = 3) : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
  intro htop
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    exact (by norm_num : (1 : ℕ) ≠ 3) hx
  have hxcent : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [htop]
      exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  haveI : IsSimpleGroup G := hC.simple
  have hcentne : Subgroup.center G ≠ ⊥ := by
    intro hbot
    rw [hbot] at hxcent
    exact hx1 (Subgroup.mem_bot.mp hxcent)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop'
  · exact hcentne hbot
  · obtain ⟨a, b, hab⟩ := hC.nonab
    have hcomm : b * a = a * b :=
      Subgroup.mem_center_iff.mp (by rw [htop']; exact Subgroup.mem_top a) b
    exact hab hcomm.symm

private theorem exists_nineSetting {M Q H E : Subgroup G} (hC : CStarGen G)
    (hM : rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty) (hHM : ¬ H ≤ M)
    (hHne : H ≠ ⊤) (hQH : Q ≤ H) (hQM : Q ≤ M) (hQ : IsPGroup 3 Q) (hEQ : E ≤ Q)
    (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 9)
    (hΓE : rankThreeGamma 1 3 E ≤ M) : NineSettingGen G M 3 Q H E 2 := by
  have hσ' : (CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M).Nonempty := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hσ
  refine { setting := ⟨hC, hM, hσ'⟩, mem_Q := ?_, mem_H := ?_, stdE := ?_ }
  · exact mem_QSet_iff.mpr ⟨Nat.prime_three, by norm_num, hQM, hQ,
      Or.inr ⟨E, hEQ, hE, by rw [hEcard]; norm_num, hΓE⟩⟩
  · exact mem_HFam_iff.mpr ⟨hHne, hQH, hHM⟩
  · exact ⟨Or.inl rfl, hEQ, hE, by rw [hEcard]; norm_num, hΓE⟩

private theorem starImg_pCoreOf_ne_bot {M Q H E : Subgroup G} (hnine : NineSettingGen G M 3 Q H E 2)
    (hO2 : pCoreOf 2 H = ⊥) (hO2M : pCoreOf 2 (H ⊓ M) ≠ ⊥) :
    starImg 3 H (pCoreOf 2 (H ⊓ M)) ≠ ⊥ := by
  intro hbot
  have hSH : pCoreOf 2 (H ⊓ M) ≤ H :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left
  have hSrel : pCoreOf 2 (H ⊓ M) ≤ relPPrimeCore 3 H :=
    hnine.le_relPPrimeCore_of_starImg_eq_bot hSH hbot
  have hSx : pCoreOf 2 (H ⊓ M) ≤ xSub 3 M H :=
    hSrel.trans (relPPrimeCore_le_xSub hnine.prime M H)
  have hS_eq : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := by
    rw [← hnine.nineEight_three, inf_eq_left.mpr hSx]
  exact hO2M (hS_eq.trans hO2)

theorem exists_component_not_centralizing {M Q H E S : Subgroup G}
    (hnine : NineSettingGen G M 3 Q H E 2) (hS2 : IsPGroup 2 S) (hSY : S ≤ H ⊓ M)
    (hSn : H ⊓ M ≤ Subgroup.normalizer (S : Set G))
    (hSne : starImg 3 H S ≠ ⊥) :
    ∃ L : Subgroup G, IsPComponentIn 3 L H ∧ ¬ L ≤ M ∧
      ¬ starImg 3 H L ≤ Subgroup.centralizer
        ((starImg 3 H S : Subgroup (StarGroup 3 H)) : Set (StarGroup 3 H)) := by
  classical
  have hSH : S ≤ H := hSY.trans inf_le_left
  have hP : starImg 3 H S ≤ Subgroup.centralizer
      ((CFSG.pCore 3 (↥H ⧸ primeComplementCore (G := ↥H) 3) :
        Subgroup (↥H ⧸ primeComplementCore (G := ↥H) 3)) :
        Set (↥H ⧸ primeComplementCore (G := ↥H) 3)) :=
    hnine.starImg_le_centralizer_pCore hS2 hSY
      (fun y hy s hs => (Subgroup.mem_normalizer_iff.mp (hSn hy) s).mp hs)
  have hex : ∃ L : Subgroup G, IsPComponentIn 3 L H ∧
      ¬ (∀ a ∈ S, ∀ l ∈ L, l * a * l⁻¹ ∈ S) ∧
      ¬ starImg 3 H L ≤ Subgroup.centralizer
        ((starImg 3 H S : Subgroup (StarGroup 3 H)) : Set (StarGroup 3 H)) := by
    by_contra hno
    have hL : ∀ L : Subgroup G, IsPComponentIn 3 L H →
        (∀ a ∈ S, ∀ l ∈ L, l * a * l⁻¹ ∈ S) ∨
          starImg 3 H L ≤ Subgroup.centralizer
            ((starImg 3 H S : Subgroup (StarGroup 3 H)) : Set (StarGroup 3 H)) := by
      intro L hL
      by_cases hN : ∀ a ∈ S, ∀ l ∈ L, l * a * l⁻¹ ∈ S
      · exact Or.inl hN
      · refine Or.inr ?_
        by_contra hC
        exact hno ⟨L, hL, hN, hC⟩
    exact hSne (hnine.starImg_eq_bot hSH hS2 hP hL)
  obtain ⟨L, hLcomp, hLnor, hLcent⟩ := hex
  refine ⟨L, hLcomp, ?_, hLcent⟩
  intro hLM
  apply hLnor
  intro a ha l hl
  exact (Subgroup.mem_normalizer_iff.mp (hSn ⟨hLcomp.1 hl, hLM hl⟩) a).mp ha

theorem o97Red_starImg (hC : CStarGen G) {M H E S : Subgroup G} (hHne : H ≠ ⊤)
    (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hEM : E ≤ M)
    (hΓE : rankThreeGamma 1 3 E ≤ M) (h3M : CFSG.Open.pRank 3 M ≤ 3)
    (h3A : 3 ∉ rankThreeSigmaA G) (hS2 : IsPGroup 2 S) (hSY : S ≤ H ⊓ M)
    (hSn : H ⊓ M ≤ Subgroup.normalizer (S : Set G)) :
    O97Red (StarGroup 3 H) (starImg 3 H E) (starImg 3 H M) (starImg 3 H S) := by
  have hEp : IsPGroup 3 E := elementary_isPGroup 3 E hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact catalogSimpleSections_starGroup
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hC.kProper H hHne)
  · exact pPrimeCore_starGroup (p := 3) Nat.prime_three
  · exact (isElemAbelian_starImg_iff Nat.prime_three hEH hEp).mpr hE
  · rw [← Nat.card_congr
      (starImgMulEquiv (p := 3) Nat.prime_three hEH hEp).toEquiv, hEcard]
  · exact starImg_mono hEM
  · refine rankThreeGamma_starImg_le (p := 3) (k := 1) Nat.prime_three hEH hEp ?_
    intro D hDE hD
    exact inf_le_left.trans
      ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 3 E M).mp hΓE D hDE hD)
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank,
      pRank_starImg_eq_pRank_inf (p := 3) Nat.prime_three M]
    exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num : 1 < 3)
      inf_le_right).trans h3M
  · intro T hT hT2
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact pRank_normalizer_starImg_le (p := 3) (r := 2) (k := 3) Nat.prime_three
      Nat.prime_two (by norm_num)
      (fun W hWne hW2 => hC.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num)
        h3A ⟨W, hWne, hW2, rfl⟩) T hT hT2
  · show IsPGroup 2 (starImg 3 H S)
    exact (hS2.comap_subtype (K := H)).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))
  · exact starImg_mono (hSY.trans inf_le_right)
  · have hY : starImg 3 H (H ⊓ M) = starImg 3 H M := by
      unfold starImg
      rw [show (H ⊓ M).subgroupOf H = M.subgroupOf H from ?_]
      ext y
      simp only [Subgroup.mem_subgroupOf]
      exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
    rw [← hY]
    exact starImg_normalizes (p := 3) (S := S) (Y := H ⊓ M)
      (fun y hy s hs => (Subgroup.mem_normalizer_iff.mp (hSn hy) s).mp hs)

private theorem exists_o98Red (hC : CStarGen G) {M H E S : Subgroup G} (hHne : H ≠ ⊤)
    (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hEM : E ≤ M)
    (hΓE : rankThreeGamma 1 3 E ≤ M) (h3M : CFSG.Open.pRank 3 M ≤ 3)
    (h3A : 3 ∉ rankThreeSigmaA G) {x : G} (hxH : x ∈ H)
    (hxc : ∀ y ∈ H, x * y = y * x) (hx : orderOf x = 3)
    (hS2 : IsPGroup 2 S) (hSY : S ≤ H ⊓ M)
    (hSn : H ⊓ M ≤ Subgroup.normalizer (S : Set G)) :
    ∃ z : StarGroup 3 H, O98Red (StarGroup 3 H) (starImg 3 H E) (starImg 3 H M)
      (starImg 3 H S) z := by
  have h := o97Red_starImg hC hHne hEH hE hEcard hEM hΓE h3M h3A hS2 hSY hSn
  let z : StarGroup 3 H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨x, hxH⟩
  have hz : z ∈ Subgroup.center (StarGroup 3 H) ∧ orderOf z = 3 :=
    starImg_zpowers_central Nat.prime_three hxH hxc hx
  exact ⟨z, ⟨h.catalog, h.core, h.elem_E, h.card_E, h.E_le, h.gamma_le, h.rank_Y, h.rank23,
    h.two_S, h.S_le, h.normal_S, hz.1, hz.2⟩⟩

theorem o98_red {G : Type} [Group G] [Finite G] (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty)
    (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) {Q : Subgroup G} (hQM : Q ≤ M)
    (hQ : IsPGroup 3 Q) (hQc : ¬ IsCyclic ↥Q) (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ M) {x : G}
    (hx : orderOf x = 3) (hxQ : ∀ y ∈ Q, x * y = y * x) {H : Subgroup G}
    (hH : H = Subgroup.centralizer ({x} : Set G)) (hHM : ¬ H ≤ M)
    (hO2 : CFSG.Open.pCoreOf 2 H = ⊥) (hO2M : CFSG.Open.pCoreOf 2 (H ⊓ M) ≠ ⊥) :
    ∃ (E L : Subgroup G) (z : AGL81C.StarGroup 3 H),
      O98Red (AGL81C.StarGroup 3 H) (AGL81C.starImg 3 H E) (AGL81C.starImg 3 H M)
        (AGL81C.starImg 3 H (CFSG.Open.pCoreOf 2 (H ⊓ M))) z ∧
      AGL81C.NineSettingGen G M 3 Q H E 2 ∧ AGL81C.IsPComponentIn 3 L H ∧ ¬ L ≤ M ∧
      ¬ AGL81C.starImg 3 H (CFSG.Open.pCoreOf 2 (H ⊓ M)) ≤
        Subgroup.centralizer ((AGL81C.starImg 3 H L : Subgroup _) : Set
          (AGL81C.StarGroup 3 H)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3A : 3 ∉ rankThreeSigmaA G := three_not_mem_sigmaA h3 hQM hQ hQc
  have h3M : CFSG.Open.pRank 3 M ≤ 3 :=
    hC.pRank_le_three_of_not_mem_sigmaSet hM Nat.prime_three (by norm_num)
      (three_not_mem_sigmaSet h3)
  obtain ⟨E, hEQ, hE, hEcard⟩ := exists_elemAbelian_nine hQ hQc
  have hEM : E ≤ M := hEQ.trans hQM
  have hΓE : rankThreeGamma 1 3 E ≤ M :=
    (CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := 3) (k := 1) hEQ).trans hΓ
  have hxH : x ∈ H := by
    rw [hH]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hxc : ∀ y ∈ H, x * y = y * x := by
    intro y hy
    rw [hH] at hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  have hQH : Q ≤ H := by
    intro y hy
    rw [hH]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hxQ y hy).symm
  have hHne : H ≠ ⊤ := by
    rw [hH]
    exact centralizer_singleton_ne_top hC hx
  have hnine : NineSettingGen G M 3 Q H E 2 :=
    exists_nineSetting hC hM hσ hHM hHne hQH hQM hQ hEQ hE hEcard hΓE
  let S : Subgroup G := pCoreOf 2 (H ⊓ M)
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 (H ⊓ M)
  have hSY : S ≤ H ⊓ M := CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)
  have hSn : H ⊓ M ≤ Subgroup.normalizer (S : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 (H ⊓ M)
  have hSne : starImg 3 H S ≠ ⊥ := starImg_pCoreOf_ne_bot hnine hO2 hO2M
  obtain ⟨L, hLcomp, hLM, hLcent⟩ :=
    exists_component_not_centralizing hnine hS2 hSY hSn hSne
  obtain ⟨z, hzO⟩ := exists_o98Red hC hHne (hEQ.trans hQH) hE hEcard hEM hΓE h3M h3A
    hxH hxc hx hS2 hSY hSn
  exact ⟨E, L, z, hzO, hnine, hLcomp, hLM,
    fun h => hLcent (Subgroup.le_centralizer_iff.mp h)⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
