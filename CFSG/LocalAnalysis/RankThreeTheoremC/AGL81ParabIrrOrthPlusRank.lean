module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitRootData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthPlus

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin

theorem le_pRank_of_dvd_card_units {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : p ∣ Nat.card Kˣ)
    (ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥Y) : r ≤ CFSG.Open.pRank p Y := by
  have h := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaPlus_torus
    (K := K) (n := r) hp hp2 hK
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      ((statedProjOmegaPlusEquiv hr).trans ρ)]
  exact h

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthPlus
