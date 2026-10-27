module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ASevenBlockAutProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem agl81TenNineOneCfg_of_nx (hCGT : AschbacherLocalCGTBlock) (hNX : NoXBlockFor G)
    (h98 : AGL81NineEightFour G) (hX : AGL81NineThreeXCfg G) (hN : AGL81TenNineNormalCfg G)
    (h3 : AGL81TenNineOneThreeCfg G) (hAut : Asc81bASevenBlockAutNX) : AGL81TenNineOneCfg G := by
  intro hS p P M H Q K hd L hL
  refine ⟨fun e => ?_⟩
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp := hesc.prime
  have hp2 := hesc.ne_two
  by_cases hp3 : p = 3
  · subst hp3
    exact (h3 hS P M H Q K hd L hL).false e
  have hLn := hN hS p P M H Q K hd hp3 L hL ⟨e⟩
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hLM : L ≤ M := hL.le
  have hMn : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hLX : ¬ InClassXBlock L := fun h =>
    hNX M L hT.toTwoLocalPair.maxTwoLocal_M hLM hL.subnormal h
  refine false_of_centralizes_cfg hS hCGT hNX hd (hX hS p P M H Q K hd) hL hLn fun b hb => ?_
  have hbM : b ∈ M := hd.base.1 hb
  exact TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hbM
    (hAut G M (pCoreOf 2 H) L hK hA hL hLX ⟨e⟩ b hbM
      (localGroup_le_normalizer_pCoreOf 2 H (hd.le_H hb))
      (coprime_six_orderOf_of_isPGroup hp hp2 hp3 hd.base.2.1 hb) (hMn hbM))

end CFSG.LocalAnalysis.RankThreeTheoremC
