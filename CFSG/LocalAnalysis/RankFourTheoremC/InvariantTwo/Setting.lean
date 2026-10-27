module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

structure KFactSetting (n : ℕ) (G : Type) [Group G] [Finite G] : Prop where
  obstruction : ObstructionSetting G
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Open.IsKProper G
  le_pRank : ∀ p ∈ rankThreeSigmaA G, ∀ P : Sylow p G, n ≤ Open.pRank p (P : Subgroup G)

theorem KFactSetting.of_d1Global (hS : D1Global G) : KFactSetting 4 G where
  obstruction := ObstructionSetting.of_d1Global hS
  simple := hS.simple
  nonab := hS.nonab
  kProper := hS.kProper
  le_pRank p hp P := four_le_pRank_sylow (mem_betaFour_of_mem_sigmaA hS.rank hp) P

end CFSG.LocalAnalysis.RankFourTheoremC
