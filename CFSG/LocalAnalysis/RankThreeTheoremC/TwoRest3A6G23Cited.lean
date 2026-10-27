module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Normal
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BNotQDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Reduction
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeModule
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizerAux
import CFSG.LocalAnalysis.AGLEmbedding.CharCore
import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
import CFSG.LocalAnalysis.AGLEmbedding.ZOneFacts
import Mathlib.Data.Nat.ModEq
import Mathlib.Dynamics.FixedPoints.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.Fitting.CharacteristicP
import Mathlib
import CFSG.Quasithin.Background.Basic
import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
import CFSG.Quasithin.EmptyFaithful.S1414Group
import CFSG.Quasithin.Background.B6Basic
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6CentralizingBase
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
import CFSG.LieType.BorelTits.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.SimpleModule.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Prop3
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycFive
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycUnique
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFCenter
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFPerfect
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFRest
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoTheoremZ
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Rest
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
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Rest3A6
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ThreeA6Sylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Close
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
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
import CFSG.HardMathSupport.Cooperstein.Transport
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3A6CubeN

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6.G23

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
  CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank {p : ℕ} (hp : 1 < p) {Q E : Subgroup G} (hEQ : E ≤ Q)
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) : 3 ≤ CFSG.Open.pRank p Q := by
  unfold CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card G, ?_⟩
    rintro k ⟨F, -, -, hF⟩
    have h1 : p ^ k ≤ Nat.card G := hF ▸ Subgroup.card_le_card_group F
    exact (Nat.lt_pow_self hp).le.trans h1
  · exact ⟨E, hEQ, hE, hc⟩

theorem exists_conj_le_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p G) {M : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) {Q : Subgroup G} (hQM : Q ≤ M) (hQ : IsPGroup p Q) :
    ∃ c ∈ M, ∀ q ∈ Q, c * q * c⁻¹ ∈ (P : Subgroup G) := by
  classical
  have hp : IsPGroup p (Q.subgroupOf M) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M T (P.subtype hPM)
  refine ⟨c, c.2, fun q hq => ?_⟩
  have hqT : (⟨q, hQM hq⟩ : M) ∈ (T : Subgroup M) := hT (Subgroup.mem_subgroupOf.mpr hq)
  have hmem : MulAut.conj c (⟨q, hQM hq⟩ : M) ∈ ((c • T : Sylow p M) : Subgroup M) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hqT
  rw [hc, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem normalizer_le_of_rank {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M T E : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hTM : T ≤ M)
    (hT : IsPGroup p T) (hET : E ≤ T) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    Subgroup.normalizer (T : Set G) ≤ M := by
  obtain ⟨x, hxM, hx⟩ := exists_conj_le_sylow P hPM hTM hT
  set Q := T.map (MulAut.conj x).toMonoidHom with hQ
  have hQP : Q ≤ (P : Subgroup G) := by
    rintro _ ⟨t, ht, rfl⟩
    simpa using hx t ht
  have hp1 : 1 < p := hp.out.one_lt
  have hEQ : E.map (MulAut.conj x).toMonoidHom ≤ Q := Subgroup.map_mono hET
  have hE' : IsElemAbelian p (E.map (MulAut.conj x).toMonoidHom) := hE.map _
  have hEc' : Nat.card (E.map (MulAut.conj x).toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hEc]
  have h3 : 3 ≤ CFSG.Open.pRank p Q := three_le_pRank hp1 hEQ hE' hEc'
  have hNQ : Subgroup.normalizer (Q : Set G) ≤ M :=
    (normalizer_le_weakCore p hQP (by omega)
      (h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp.out le_sup_left))).trans hcore
  intro g hg
  have hxg : x * g * x⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
    refine mem_normalizer_of_conj_mem fun q hq => ?_
    obtain ⟨t, ht, rfl⟩ := hq
    refine ⟨g * t * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg t).mp ht, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have := hNQ hxg
  have hg' : g = x⁻¹ * (x * g * x⁻¹) * x := by group
  rw [hg']
  exact M.mul_mem (M.mul_mem (M.inv_mem hxM) this) hxM

theorem normalizer_zpowers_le {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M E : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) {a : G}
    (haE : a ∈ E) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hC : Subgroup.centralizer ({a} : Set G) ≤ M) :
    Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ M := by
  classical
  set C := Subgroup.centralizer ({a} : Set G) with hCdef
  have hEC : E ≤ C := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    rintro y rfl
    exact congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨y, haE⟩ ⟨e, he⟩)
  obtain ⟨T, hT⟩ := (hE.isPGroup.comap_subtype (K := C)).exists_le_sylow
  set T' := (T : Subgroup C).map C.subtype with hT'
  have hT'C : T' ≤ C := Subgroup.map_subtype_le _
  have hET' : E ≤ T' := fun e he =>
    ⟨⟨e, hEC he⟩, hT (show (⟨e, hEC he⟩ : C) ∈ E.comap C.subtype from he), rfl⟩
  have hT'p : IsPGroup p T' := T.isPGroup'.map _
  have hNT : Subgroup.normalizer (T' : Set G) ≤ M :=
    normalizer_le_of_rank hPM hcore (hT'C.trans hC) hT'p hET' hE hEc
  intro n hn
  have hnC : ∀ x ∈ C, n * x * n⁻¹ ∈ C := by
    intro x hx
    have ha' : n⁻¹ * a * n ∈ Subgroup.zpowers a := by
      apply (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * a * n)).mpr
      have : n * (n⁻¹ * a * n) * n⁻¹ = a := by group
      rw [this]; exact Subgroup.mem_zpowers a
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha'
    have hxa : a * x = x * a := (Subgroup.mem_centralizer_iff.mp hx) a (Set.mem_singleton a)
    have hxk : a ^ k * x = x * a ^ k := (Commute.zpow_left (show Commute a x from hxa) k).eq
    have ha_eq : a = n * a ^ k * n⁻¹ := by rw [hk]; group
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    calc a * (n * x * n⁻¹) = n * (a ^ k * x) * n⁻¹ := by
          conv_lhs => rw [ha_eq]
          group
      _ = n * (x * a ^ k) * n⁻¹ := by rw [hxk]
      _ = n * x * n⁻¹ * a := by
          conv_rhs => rw [ha_eq]
          group
  set T2 : Subgroup C := (T'.map (MulAut.conj n).toMonoidHom).subgroupOf C with hT2
  have hle2 : T'.map (MulAut.conj n).toMonoidHom ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    exact hnC t (hT'C ht)
  have hcard2 : Nat.card T2 = Nat.card (T : Subgroup C) := by
    rw [hT2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle2).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj n).injective, hT',
      Subgroup.card_map_of_injective C.subtype_injective]
  let S2 : Sylow p C := Sylow.ofCard T2 (by rw [hcard2]; exact T.card_eq_multiplicity)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C T S2
  have hcn : (c : G)⁻¹ * n ∈ Subgroup.normalizer (T' : Set G) := by
    refine mem_normalizer_of_conj_mem fun t ht => ?_
    have h1 : n * t * n⁻¹ ∈ C := hnC t (hT'C ht)
    have h2 : (⟨n * t * n⁻¹, h1⟩ : C) ∈ ((c • T : Sylow p C) : Subgroup C) := by
      rw [hc]
      show (⟨n * t * n⁻¹, h1⟩ : C) ∈ T2
      exact Subgroup.mem_subgroupOf.mpr ⟨t, ht, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
    refine ⟨_, h2, ?_⟩
    simp [MulAut.inv_apply]
    group
  have hcM : (c : G) ∈ M := hC c.2
  have hn' : n = (c : G) * ((c : G)⁻¹ * n) := by group
  rw [hn']
  exact M.mul_mem hcM (hNT hcn)

theorem inf_le_pCoreOf {L M : Subgroup G} (hLM : L ≤ M) : L ⊓ pCoreOf 2 M ≤ pCoreOf 2 L := by
  refine normal_pGroup_le_pCoreOf 2 _ L inf_le_left ?_
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_right)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun l hl => ?_
  have h1 : l ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 M (hLM hl)
  rw [Subgroup.mem_normalizer_iff] at h1 ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 y]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨L.mul_mem (L.mul_mem hl hy) (L.inv_mem hl), h⟩
  · rintro ⟨hy, h⟩
    refine ⟨?_, h⟩
    have : y = l⁻¹ * (l * y * l⁻¹) * l := by group
    rw [this]
    exact L.mul_mem (L.mul_mem (L.inv_mem hl) hy) hl

end CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6.G23

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6.G23
  CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

structure TwoRestG23Config (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)) (z : H)
    (Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (L : Subgroup G) : Prop where
  data : D1CaseTwoData3 3 P M H R Rbar
  cand : D1CaseTwoCand 3 M H R z
  notSP : ¬ D1CzSP 3 (z : G)
  outside : D1CzOutside 3 (z : G)
  b0 : D1CzB0 3 R (z : G)
  twoCore : pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥
  even : D1CzEven 3 (z : G)
  kAxis : D1CaseTwoKAxis 3 P M R (z : G)
  normalizer_le : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
    (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H
  component : IsComponentOf Kbar ⊤
  not_le : ¬ Kbar ≤ d1X0 3 M H
  block : IsWeakSBlock M (pCoreOf 2 H) L
  center : Nat.card (Subgroup.center ↥(barM M L)) = 3
  quot : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))
  centV : CenterCentralizesBlockV M (pCoreOf 2 H) L block.le
  notShort : ¬ IsShort2 L

@[expose] def TwoRestTenFourteen (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (z : H) (Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (L : Subgroup G),
    TwoRestG23Config P M H R Rbar z Kbar L →
    ∀ a : G, a ≠ 1 → a ^ 3 = 1 →
      (∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ a ∈ E) →
      ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
      ¬ ⁅Subgroup.zpowers a, L⁆ ≤ pCoreOf 2 L

end CFSG.LocalAnalysis.RankThreeTheoremC
