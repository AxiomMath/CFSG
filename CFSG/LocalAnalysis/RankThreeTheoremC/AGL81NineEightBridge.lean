module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Adapters.GeneralizedFittingTop
import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
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
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
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

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsStdE)

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_of_card {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : 3 ≤ Open.pRank p E :=
  le_csSup (pRank_bddAbove p hp E) ⟨E, le_rfl, hE, hEc⟩

theorem glbCore_two_le_of_escape {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (he : D1Escape p P M H R) {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : GLBCore p 2 E ≤ M := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := IsPGroup.of_card hEc
  obtain ⟨m, hm, hEP⟩ := exists_conj_le he.sylow_le hEp hEM
  have hW := weakCore_conj_le hp he.weakCore_le hm
  refine sSup_le ?_
  rintro N ⟨X, hXE, hX2, rfl⟩
  refine (normalizer_le_weakCore p (hXE.trans hEP) hX2 ?_).trans hW
  refine (three_le_pRank_of_card hp hE hEc).trans (pRank_mono p hp ?_)
  refine fun e he' => (le_sup_right : _ ≤ X ⊔ _) ⟨hEP he', Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro x hx
  have := isMulCommutative_iff.mp hE.1 ⟨x, hXE hx⟩ ⟨e, he'⟩
  simpa using congrArg Subtype.val this

theorem exists_isStdE_of_isAGLQ {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (he : D1Escape p P M H R) {Q : Subgroup G} (hQ : IsAGLQ p M Q) :
    ∃ k : ℕ, ∃ E : Subgroup G, IsStdE p k M Q E := by
  have hp := he.prime
  obtain ⟨hQM, -, hQ3⟩ := hQ
  rcases hQ3 with h3 | ⟨E, hEQ, hE, hEc, hΓ⟩
  · obtain ⟨E₀, hE₀Q, hE₀, hE₀c⟩ := pRank_attained p hp Q
    have h3' : 3 ≤ Open.pRank p Q := by rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    have hdvd : p ^ 3 ∣ Nat.card E₀ := hE₀c ▸ pow_dvd_pow p h3'
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
    refine ⟨3, F.map E₀.subtype, Or.inr rfl, (Subgroup.map_subtype_le F).trans hE₀Q,
      IsElemAbelian.mono hE₀ (Subgroup.map_subtype_le F), ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective E₀.subtype_injective, hF]
    · exact glbCore_two_le_of_escape he ((Subgroup.map_subtype_le F).trans (hE₀Q.trans hQM))
        (IsElemAbelian.mono hE₀ (Subgroup.map_subtype_le F))
        (by rw [Subgroup.card_map_of_injective E₀.subtype_injective, hF])
  · exact ⟨2, E, Or.inl rfl, hEQ, hE, hEc, hΓ⟩

theorem isComponentOf_top_of_isComponent' {X : Type*} [Group X] {L : Subgroup X}
    (hL : CFSG.IsComponent L) : IsComponentOf L ⊤ :=
  ⟨le_top, (CFSG.Adapters.isSubnormal_top_iff L).mpr hL.2,
    ⟨hL.1.1.commutator_eq_top, hL.1.2.1⟩⟩

theorem kStar_le_d1KBar {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    (hJ : ¬ AGL81C.pLayerIn p H ≤ M)
    (hcore : (primeComplementCore (G := H) p).map H.subtype ≤ M) :
    AGL81C.kStar p M H ≤ d1KBar p M H := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  have key : ∀ Y : Subgroup G, AGL81C.IsPComponentIn p Y H → ¬ Y ≤ M →
      (Y.subgroupOf H).map π ≤ d1KBar p M H := by
    intro Y hY hYM
    obtain ⟨K, hKc, -, hYK, -⟩ := hY.2
    have hK : IsComponentOf ((Y.subgroupOf H).map π) ⊤ := by
      have : (Y.subgroupOf H).map π = K := hYK
      rw [this]
      exact isComponentOf_top_of_isComponent' hKc
    refine le_d1KBar hK fun hle => hYM fun y hy => ?_
    obtain ⟨⟨m, hmH⟩, hm, hmy⟩ := hle ⟨⟨y, hY.1 hy⟩, hy, rfl⟩
    have ho : (⟨m, hmH⟩ : H)⁻¹ * ⟨y, hY.1 hy⟩ ∈ primeComplementCore (G := H) p := by
      rw [← QuotientGroup.eq_one_iff]
      show π ((⟨m, hmH⟩ : H)⁻¹ * ⟨y, hY.1 hy⟩) = 1
      rw [map_mul, map_inv, hmy, inv_mul_cancel]
    have hoM : ((⟨m, hmH⟩ : H)⁻¹ * ⟨y, hY.1 hy⟩ : H).1 ∈ M := hcore ⟨_, ho, rfl⟩
    have e : y = m * ((⟨m, hmH⟩ : H)⁻¹ * ⟨y, hY.1 hy⟩ : H).1 := by simp
    rw [e]
    exact M.mul_mem (Subgroup.mem_subgroupOf.mp hm).2 hoM
  have hS : sSup {Y : Subgroup G | AGL81C.IsPComponentIn p Y H ∧ ¬ Y ≤ M} ≤
      ((d1KBar p M H).comap π).map H.subtype :=
    sSup_le fun Y ⟨hY, hYM⟩ y hy =>
      ⟨⟨y, hY.1 hy⟩, key Y hY hYM ⟨⟨y, hY.1 hy⟩, hy, rfl⟩, rfl⟩
  unfold AGL81C.kStar AGL81C.kSub
  rw [if_neg hJ]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x', hx', hxx⟩ := hS (Subgroup.mem_subgroupOf.mp hx)
  have : x' = x := Subtype.ext hxx
  rw [← this]
  exact hx'

theorem isComponent_of_isComponentOf_top'' {X : Type*} [Group X] {L : Subgroup X}
    (hL : IsComponentOf L ⊤) : CFSG.IsComponent L :=
  ⟨⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩,
    (CFSG.Adapters.isSubnormal_top_iff L).mp hL.2.1⟩

theorem d1KBar_le_kStar {p : ℕ} {M H : Subgroup G} (hJ : ¬ AGL81C.pLayerIn p H ≤ M) :
    d1KBar p M H ≤ AGL81C.kStar p M H := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  refine iSup₂_le fun L hL => ?_
  obtain ⟨hLc, hLX⟩ := hL
  obtain ⟨Y', hY', hYL⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent
    p (isComponent_of_isComponentOf_top'' hLc)
  have hYL' : Y'.map π = L := hYL
  set Y : Subgroup G := Y'.map H.subtype with hY
  have hYY : Y.subgroupOf H = Y' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hYin : AGL81C.IsPComponentIn p Y H := ⟨Subgroup.map_subtype_le _, hYY ▸ hY'⟩
  have hYM : ¬ Y ≤ M := by
    intro hle
    refine hLX ?_
    rw [← hYL']
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, ⟨y.2, hle ⟨y, hy, rfl⟩⟩, rfl⟩
  have hYK : Y ≤ AGL81C.kSub p M H := by
    unfold AGL81C.kSub
    rw [if_neg hJ]
    exact le_sSup ⟨hYin, hYM⟩
  rw [← hYL']
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hYK ⟨y, hy, rfl⟩, rfl⟩

theorem kStar_eq_d1KBar {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    (hJ : ¬ AGL81C.pLayerIn p H ≤ M)
    (hcore : (primeComplementCore (G := H) p).map H.subtype ≤ M) :
    AGL81C.kStar p M H = d1KBar p M H :=
  le_antisymm (kStar_le_d1KBar hJ hcore) (d1KBar_le_kStar hJ)

theorem sSup_invTwoSubgroups_le_xSub {p : ℕ} [Fact p.Prime] {M H Q : Subgroup G}
    (hJ : ¬ AGL81C.pLayerIn p H ≤ M)
    (hcore : (primeComplementCore (G := H) p).map H.subtype ≤ M)
    (hb3 : Hyp111B3 p H Q (d1KBar p M H)) :
    sSup (AGL81C.invTwoSubgroups H Q) ≤ AGL81C.xSub p M H := by
  have hKK := kStar_le_d1KBar hJ hcore
  refine sSup_le fun R hR => (hb3 R hR.2.1 hR.1 hR.2.2).trans ?_
  unfold AGL81C.xSub d1PlusCore
  exact Subgroup.map_mono (Subgroup.comap_mono (Subgroup.centralizer_le hKK))

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
