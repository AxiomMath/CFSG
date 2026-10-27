module

public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.RankThree.PartOne.LIT.KFCGTList
public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeAux
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.RankThree.PartOne.S12.SectionalRank

public section

namespace CFSG.AGLEmbedding

open CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.RankThree.PartOne

namespace NoXBlock

variable {G : Type} [Group G] [Finite G]

theorem evenRank_le_two_of_inOmegaK (h1 : AschbacherTheoremOneK) (h2 : AschbacherTheoremTwoK)
    (h25 : SolomonAlternatingBlockK) (hKP : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hsimple : IsSimpleGroup G) (hchar : CFSG.Assembly.IsCharTwoType G) {Y : Subgroup G}
    (hY : InOmega Y) : CFSG.Assembly.evenRank G ≤ 2 := by
  obtain ⟨X, hX, hmax⟩ := exists_arrow_maximal hY
  obtain ⟨N₀, hN₀⟩ := h1 G hKP hchar X hX hmax
  obtain ⟨hXcls, N, hN, hXN, hXNsub⟩ := hX
  have hNeq : CFSG.maximalTwoLocalsContaining (X : Set G) = {N} := by
    have hmem : N ∈ CFSG.maximalTwoLocalsContaining (X : Set G) := ⟨hN, hXN⟩
    rw [hN₀, Set.mem_singleton_iff] at hmem
    rw [hN₀, hmem]
  rcases hXcls.2 with ⟨n, hn, halt⟩ | ⟨n, hn, hlin⟩
  · exact evenRank_le_two_of_sectionalTwoRankLEFour hchar
      (h25 G hKP hsimple hchar N X hN hXN hXNsub hXcls ⟨n, hn, halt⟩ hNeq)
  · have h2n : 2 ≤ n := by
      by_contra hlt
      obtain rfl : n = 1 := by omega
      exact not_isNaturalSLTwoModule_one hXcls.1 hlin
    rcases h2 G hKP hsimple hchar X N hXcls hN hXN hXNsub hNeq n h2n hlin with h | h | ⟨-, h⟩
    · exact kfCGTList G hchar (Or.inl ⟨n, hn, Or.inr (Or.inr (Or.inl h))⟩)
    · exact kfCGTList G hchar (Or.inl ⟨n, hn, Or.inr (Or.inr (Or.inr h))⟩)
    · exact evenRank_le_two_of_sectionalTwoRankLEFour hchar (sectionalTwoRankLE_four_of_eq h)

end NoXBlock

open NoXBlock in
theorem d1NoXBlock_of_inputsK (h1 : AschbacherTheoremOneK) (h2 : AschbacherTheoremTwoK)
    (h25 : SolomonAlternatingBlockK) : D1NoXBlock := by
  intro G _ _ hD M Y hM hYM hsub hY
  have hrank : 3 ≤ CFSG.Assembly.evenRank G := (open_evenRank_eq (G := G)) ▸ hD.rank
  have hle := evenRank_le_two_of_inOmegaK h1 h2 h25
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp hD.kProper) hD.simple
    (assembly_isCharTwoType_of_open hD.charTwo)
    ⟨inClassX_of_inClassXBlock hY, M, isMaximalTwoLocal_of_glb hM, hYM,
      isSubnormal_subgroupOf_of_open hsub⟩
  omega

end CFSG.AGLEmbedding
