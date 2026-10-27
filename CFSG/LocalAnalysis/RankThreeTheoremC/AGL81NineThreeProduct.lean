module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux
import CFSG.Adapters.LinearCatalog
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
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
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
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

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding

theorem isSimpleGroup_of_isNineThreeProductIndex {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsNineThreeProductIndex p d) : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  rcases hd with ⟨-, q, hqp, hqe, hdq⟩ | ⟨-, hdq⟩
  · dsimp only at hdq
    subst hdq
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have h4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
      rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hqp, hqe]
      norm_num
    exact (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).isSimpleGroup_congr.2
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := GaloisField q.p q.exponent) h4)
  · dsimp only at hdq
    subst hdq
    haveI := (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 2 (by norm_num)).1
    exact (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).isSimpleGroup

theorem nineThreeListGroup_sup_of_components {X : Type} [Group X] [Finite X] {p : ℕ}
    {L₁ L₂ : Subgroup X} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsNineThreeProductIndex p d)
    (e₁ : L₁ ≃* (TauCeti.CFSGIndex.lie d).Group) (e₂ : L₂ ≃* (TauCeti.CFSGIndex.lie d).Group) :
    NineThreeListGroup p (L₁ ⊔ L₂ : Subgroup X) := by
  haveI := isSimpleGroup_of_isNineThreeProductIndex hd
  haveI : IsSimpleGroup L₁ := e₁.isSimpleGroup
  have hC : L₁ ≤ Subgroup.centralizer (L₂ : Set X) := le_centralizer_of_component_ne h₁ h₂ hne
  have hZ : Subgroup.center L₁ = ⊥ := by
    refine (Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center L₁)).resolve_right fun htop => ?_
    haveI := h₁.2.2.2
    obtain ⟨y, hy⟩ := exists_ne (1 : L₁ ⧸ Subgroup.center L₁)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    exact hy ((QuotientGroup.eq_one_iff y).mpr (by rw [htop]; exact Subgroup.mem_top y))
  have hcomm : ∀ (a : L₁) (b : L₂), Commute (L₁.subtype a) (L₂.subtype b) := fun a b =>
    ((Subgroup.mem_centralizer_iff.mp (hC a.2)) b b.2).symm
  have hdisj : Disjoint L₁.subtype.range L₂.subtype.range := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
    intro x hx₁ hx₂
    have hx : (⟨x, hx₁⟩ : L₁) ∈ Subgroup.center L₁ := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hC g.2)) x hx₂).symm
    rw [hZ, Subgroup.mem_bot] at hx
    exact congrArg Subtype.val hx
  have hinj := (MonoidHom.noncommCoprod_injective L₁.subtype L₂.subtype hcomm).mpr
    ⟨L₁.subtype_injective, L₂.subtype_injective, hdisj⟩
  have hrange : (MonoidHom.noncommCoprod L₁.subtype L₂.subtype hcomm).range = L₁ ⊔ L₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact Or.inr ⟨d, hd, ⟨((MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr hrange)).symm.trans (e₁.prodCongr e₂)⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
