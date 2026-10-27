module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ComponentCases3
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ComponentSL3
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterExtraspecial

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open
open CFSG.AGLEmbedding (prime_dvd_card_center_quotient_of_isComponentOf)

variable {G : Type} [Group G] [Finite G]

theorem D1ComponentBetaData3.three_le_pRank {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentBetaData3 p P M H R z Pbar zbar K) :
    3 ≤ Open.pRank p (⊤ : Subgroup (MulAut K)) := by
  have hp : p.Prime := Fact.out
  have : K.Normal := h.data.normal
  obtain ⟨E, L, hER, hEcard, hEexp, hEZ, e, hSL⟩ := h.data.exists_extraspecial
  have hKp : p ∣ Nat.card K :=
    (prime_dvd_card_center_quotient_of_isComponentOf hp h.data.red.core_eq_bot h.data.comp).trans
      (Subgroup.card_quotient_dvd_card _)
  exact three_le_pRank_mulAut_of_outer_extraspecial Pbar h.center_eq_bot hKp
    h.data.zbar_mem_center h.data.zbar_order h.cyclic hER hEcard hEexp hEZ e hSL

theorem d1ComponentBetaSmallCase3 : D1ComponentBetaSmallCase3 G := by
  intro p _ P M H R z Pbar zbar K hd _ hAut
  have := hd.three_le_pRank
  omega

theorem d1CentralizerBetaSmallCase3 : D1CentralizerBetaSmallCase3 G :=
  d1ComponentBetaSmallCase3.centralizer

theorem d1SylowBetaSmallCase3 : D1SylowBetaSmallCase3 G :=
  d1ComponentBetaSmallCase3.sylow

end CFSG.LocalAnalysis.RankThreeTheoremC
