module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeTheoremBStar
public import CFSG.CharacterTheory.Semidihedral.AllPrimeStationaryCoverage
public import CFSG.CharacterTheory.Semidihedral.AllPrimeR1NFacts
public import CFSG.CharacterTheory.Semidihedral.AllPrimeV4Inputs42
public import CFSG.CharacterTheory.Semidihedral.AllPrimeV4Inputs46
public import CFSG.CharacterTheory.Semidihedral.AllPrimeV4Inputs49
public import CFSG.CharacterTheory.Semidihedral.AllPrimeIV9Reflection
public import CFSG.LocalAnalysis.ABGTheoremB.QGroupSignalizer
public import CFSG.LocalAnalysis.ABGTheoremB.IV9DGroupInputs
public import CFSG.LocalAnalysis.ABGTheoremB.IV9KFacts
public import CFSG.LocalAnalysis.ABGTheoremB.II61QBridge
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusDConjugacyQD
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DGroupCentralizerQD
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.InputsFourFusionQD
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion CFSG.ABGTheoremB.TotallyInverted

theorem frontier_qdBStarInputs
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    :
    (frontierSetting S fS t p f).QDBStarInputs := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  have hII := frontier_chapterIIFacts hGnonab hrec n hn S fS t ht hnonab hcentral hnc p f hp hpodd
    hf hq hmodel
  exact {
    r1N := frontier_R1NFacts hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
    II417 := (frontierSetting S fS t p f).IV9_h_II417 hσ hII hII.toNStructure
    II510 := frontier_II510 hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
    II61Q := (frontierSetting S fS t p f).II61Q_of_qGroup hσ hII
    v42 := frontier_lemmaII42Input hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel
    v49 := frontier_lemmaII49Input hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel
    v46 := frontier_lemmaII46Input hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel
    qSig := (frontierSetting S fS t p f).qGroupSignalizerInput_of hσ
      (frontier_nStructure hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel)
      (frontier_x₂_commutator_mem_ON hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
        hq hmodel)
    dSig := (frontierSetting S fS t p f).dGroupSignalizerInput_of hσ
    v87D := fun _ hr hr2 => abg_V_8_7_D_input_of hσ hr hr2 (abg_II_5_7_input_of hσ)
    dFourFusion := Inputs.dGroupFourFusion_of_semidihedral G }

theorem frontier_theoremBStar
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).TheoremBStar :=
  frontier_theoremBStar_of hGnonab hrec n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel (frontier_qdBStarInputs hGnonab hrec n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
      hq hmodel)

theorem stationaryCoverageStatement
    : SimpleLayerFrontier.StationaryCoverageStatement :=
  stationaryCoverageStatement_of_theoremBStar
    fun _ _ _ _ hGnonab hrec n hn S fS t ht _ hnonab hcentral hnc p f hp hpodd hf hq hmodel =>
      frontier_theoremBStar hGnonab hrec n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
        hmodel

end CFSG.Semidihedral.AllPrime
