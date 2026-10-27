module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineConseq
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.Base
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTwelveThirteenKerSetup
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.GroupTheory.LocalCores.Components
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
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenCF
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenStar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem starImg_pLayerIn_normal (hp : p.Prime) (H : Subgroup G) :
    (starImg p H (pLayerIn p H)).Normal := by
  have : (CFSG.layer (StarGroup p H)).Characteristic := CFSG.LocalCores.layer_characteristic
  rw [starImg_pLayerIn hp H]
  infer_instance

theorem cStarL_normal_of_prime (hp : p.Prime) (H : Subgroup G) : (cStarL p H).Normal := by
  have : (CFSG.layer (StarGroup p H)).Characteristic := CFSG.LocalCores.layer_characteristic
  rw [cStarL_eq_centralizer_layer hp H]
  infer_instance

theorem isPGroup_of_isHomocyclicRank2 {X : Type} [Group X] (hX : IsHomocyclicRank2 p X) :
    IsPGroup p X := by
  obtain ⟨n, -, ⟨e⟩⟩ := hX
  refine IsPGroup.of_card (n := n + n) ?_
  have h : Nat.card (Multiplicative (ZMod (p ^ n))) = p ^ n := Nat.card_zmod _
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, h, pow_add]

theorem kStar_le_oPPrimeHull (hp : p.Prime) (hL : pLayerIn p H ≤ M) :
    kStar p M H ≤ oPPrimeHull p (kStar p M H) := by
  have hK := kStar_eq_closure_of_le hp hL
  calc kStar p M H = closure {x : StarGroup p H | orderOf x = p} := hK
    _ ≤ oPPrimeHull p (kStar p M H) := (Subgroup.closure_le _).mpr fun x hx =>
        Subgroup.subset_closure ⟨by rw [hK]; exact Subgroup.subset_closure hx, 1, by
          rw [pow_one]; exact hx⟩

theorem kStar_le_oPPrimeHull_top (hp : p.Prime) (hL : pLayerIn p H ≤ M) :
    kStar p M H ≤ oPPrimeHull p (⊤ : Subgroup (StarGroup p H)) := by
  rw [kStar_eq_closure_of_le hp hL]
  exact (Subgroup.closure_le _).mpr fun x hx =>
    Subgroup.subset_closure ⟨Subgroup.mem_top x, 1, by rw [pow_one]; exact hx⟩

namespace NineSettingGen

theorem pCore_star_le_starImg (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) (hU : NineNineOne M p) :
    CFSG.pCore p (StarGroup p H) ≤ starImg p H M := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, -, -, -, ⟨S, hS⟩, hPM, -⟩ := h.exists_sylow_nineSetting hH2 hp hU
  have h1 : CFSG.pCore p (StarGroup p H) ≤
      (S.mapSurjective (QuotientGroup.mk'_surjective (primeComplementCore (G := ↥H) p)) :
        Subgroup (StarGroup p H)) :=
    IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup _
  rw [Sylow.coe_mapSurjective] at h1
  refine h1.trans (Subgroup.map_mono fun x hx => ?_)
  have hxP : (x : G) ∈ P := by
    rw [← hS]
    exact ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr (hPM hxP)

theorem mem_of_mk_mem_starImg (h : NineSettingGen G M p Q H E k) {x : ↥H}
    (hx : (QuotientGroup.mk x : StarGroup p H) ∈ starImg p H M) : (x : G) ∈ M := by
  obtain ⟨y, hy, hyx⟩ := hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
  have h2 : ((y⁻¹ * x : ↥H) : G) ∈ M := by
    apply h.relPPrimeCore_le
    rw [nineTenGen_relPPrimeCore_eq_map h.prime H]
    exact ⟨_, hyx, rfl⟩
  have hxy : (x : G) = (y : G) * ((y⁻¹ * x : ↥H) : G) := by simp
  rw [hxy]
  exact M.mul_mem (Subgroup.mem_subgroupOf.mp hy) h2

theorem mem_kerIn_of_mk_mem (h : NineSettingGen G M p Q H E k) {K : Subgroup G} (hKH : K ≤ H)
    {F : Subgroup (StarGroup p H)} (hF : F.Normal) (hFM : F ≤ starImg p H M) (a : ↥K)
    (ha : (QuotientGroup.mk (Subgroup.inclusion hKH a) : StarGroup p H) ∈ F) :
    (a : G) ∈ kerIn M K := by
  refine mem_kerIn_iff_forall_conj.mpr ⟨a.2, fun c hc => ?_⟩
  have hmem : (QuotientGroup.mk (⟨c, hKH hc⟩ * Subgroup.inclusion hKH a * ⟨c, hKH hc⟩⁻¹ : ↥H) :
      StarGroup p H) ∈ F := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hF.conj_mem _ ha _
  exact h.mem_of_mk_mem_starImg (hFM hmem)

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
