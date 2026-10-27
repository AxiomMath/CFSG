module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GExcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZGold
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZNorm
public import CFSG.Assembly.OddCoreSpan
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineCanonicalRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoStrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412

theorem sec5g_of_goldData (hGold : GoldStmt) (hN11a : S_N11a)
    (hN11b : S_N11b) {X : Type} [Group X] [Finite X] {Sb Tb : Subgroup X}
    (hP : ∃ P : Sylow 2 X, (P : Subgroup X) = Sb) (hd : Sec5ZGoldData Sb Tb)
    (hIII : ¬ Sec5GCaseIII Sb Tb) : Sec5GOutcome Sb Tb := by
  obtain ⟨P, rfl⟩ := hP
  rcases sec5g_trichotomy hGold hN11a hN11b P Tb hd.le hd.comm hd.sq hd.card hd.closed
    hd.trans with h | h
  · exact h
  · exact absurd h hIII

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

theorem sec5g_main (hGold : GoldStmt) (hN11a : S_N11a)
    (hN11b : S_N11b) (hy : Sec5B59Hyp) (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d)
    (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6) (hD : Asc82FactQCentOrd6)
    (hU : Asc82FactPocketsUniq6) (h : Sec510Ctx G t L S z r ρ B A φ)
    (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hTE : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) = sec5p510_E t a b)
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X) (hπ : Function.Surjective π)
    (hker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G))) :
    Sec5GOutcome ((S.subgroupOf (centralizer ({z} : Set G))).map π)
      (((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
        (centralizer ({z} : Set G))).map π) := by
  haveI : Finite X := Finite.of_surjective π hπ
  refine sec5g_of_goldData hGold hN11a hN11b (sec5z_exists_sylow_quotient h π hπ)
    (sec5z_gold_data hy h55 h58d hFB h4 h hs hTE π hπ hker) ?_
  refine sec5g_not_caseIII π hker
    (fun s hs' => Subgroup.mem_centralizer_singleton_iff.mpr (h.central s hs')) hs.pk.Q_le_S
    (sec5z_S_le_normalizer_Q hy hU h.toSec5Ctx hs.pk) (sec5g_Q_extraspecial hs.pk.q h.pocket.1)
    hs.pk.q.center h.pocket.1 (fun x hx => sec5g_Q_sq hs.pk.q hx) rfl
    (sec5p510_R_card_dvd hy hD h.toSec5Ctx hs.pk.q hs.cs) (sec5p510_T_le_R t z _) ?_
  rw [hTE]
  exact sec5p510_z_mem_E h hs.ab

end CFSG.OddStandard.SmallF3.Omega
