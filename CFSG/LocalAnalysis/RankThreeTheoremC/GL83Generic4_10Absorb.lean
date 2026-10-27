module

import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_isTwoLocal_of_three_le_pRank (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {R E H : Subgroup G} (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hEe : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hEM : E ≤ M) (hER : E ≤ centralizer (R : Set G)) (hH : IsTwoLocal H) (hRH : R ≤ H)
    (hH3 : 3 ≤ CFSG.Open.pRank p H) : H ≤ M := by
  have : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨E', hE'H, hE'e, hE'c⟩ := pRank_attained p H (by omega)
  obtain ⟨P'', hE'P''⟩ := (elementary_isPGroup p E' hE'e).exists_le_sylow
  obtain ⟨M'', hM'', hP''M'', -, -, -⟩ := exists_isCoreMaxLocal hS hp P''
  have hHM'' : H ≤ M'' := le_of_three_le_pRank_inf hD1 hp hM'' hH
    (le_trans (by omega) (le_pRank_of_elemAbelian_card
      (le_inf hE'H (hE'P''.trans hP''M'')) hE'e hE'c))
  have hNR : normalizer (R : Set G) ≤ M'' :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM'' (elementary_isPGroup p R hRe)
      (hRH.trans hHM'') (le_pRank_of_elemAbelian_card le_rfl hRe hRc)
  have hM''M : M'' ≤ M := le_of_three_le_pRank_inf hD1 hp hM hM''.1.1
    (le_pRank_of_elemAbelian_card
      (le_inf (hER.trans ((centralizer_le_normalizer _).trans hNR)) hEM) hEe hEc)
  exact hHM''.trans hM''M

end CFSG.LocalAnalysis.RankThreeTheoremC
