module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductions
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridge
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GuestConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreePairStrong
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate43

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem le_four_of_blockPLThreeSolv_perm {M S L : Subgroup G} (hsolv : BlockPLThreeSolv M S L)
    {n : ℕ}
    (e : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin n)) :
    n ≤ 4 := by
  by_contra hn
  obtain ⟨Y, hYP, hY, h3⟩ := exists_perfect_three_dvd_of_surjective_perm (by omega : 5 ≤ n)
    (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact hsolv Y hYP hY h3

theorem NineThreeSix.le_four {M S L : Subgroup G} (h : NineThreeSix M S L)
    (hsolv : BlockPLThreeSolv M S L) :
    ∃ n : ℕ, n ≤ 4 ∧ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
      alternatingGroup (Fin (2 * n))) := by
  obtain ⟨-, n, hA, ⟨e⟩⟩ := h
  exact ⟨n, le_four_of_blockPLThreeSolv_perm hsolv e, hA⟩

theorem NineThreeSeven.le_four {M S L : Subgroup G} (h : NineThreeSeven M S L)
    (hsolv : BlockPLThreeSolv M S L) :
    ∃ n : ℕ, n ≤ 4 ∧ Nonempty (↥(barM M L) ≃* alternatingGroup (Fin (4 * n))) := by
  obtain ⟨-, n, hA, ⟨e⟩⟩ := h
  exact ⟨n, le_four_of_blockPLThreeSolv_perm hsolv e, hA⟩

theorem not_nineThreeEight {M S L : Subgroup G} (h : NineThreeEight M S L)
    (hsolv : BlockPLThreeSolv M S L) : False := by
  obtain ⟨-, N, r, hN, hr, h0, h2, h4, -, φ, -⟩ := h
  have hle : N - 2 * r ≤ 4 := by
    by_contra hn
    obtain ⟨Y, hYP, hY, h3⟩ := exists_perfect_three_dvd_of_surjective_perm (by omega : 5 ≤ N - 2 * r)
      ((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (QuotientGroup.mk' _)))
      ((Prod.snd_surjective).comp (φ.surjective.comp (QuotientGroup.mk'_surjective _)))
    exact hsolv Y hYP hY h3
  obtain ⟨k, hk⟩ := hN
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
