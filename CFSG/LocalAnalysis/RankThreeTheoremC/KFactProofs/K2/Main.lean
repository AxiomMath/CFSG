module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Quotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Normal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.EndGame
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Pullback
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

theorem k2Grp_of_core (hcore : KFactRankThreeCore) : K2Grp := by
  intro G _ _ Y Q h
  have hbar := h.quotient
  have hBot := primeComplementCore_bar (G := G)
  obtain ⟨L, hLn, hLs, hLnab, hL3, hLc⟩ := hbar.exists_simple_normal hBot
  have hLY : ¬ L ≤ Y.map (barMk G) := fun hle => hbar.not_normal_le hLn hL3 hle
  have hγ := hbar.gammaQ_le
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let QS : Sylow 3 (Bar G) := hbar.pgroup.toSylow hbar.index
  obtain ⟨he, hidx⟩ := hcore (Bar G) hbar.catalog hBot L hLn hLs hLnab hLc QS hbar.rank hbar.elt
    (fun hle => hLY (hle.trans hγ))
  exact K2Concl.of_bar (exists_index_three_normal hLn he hLc hidx)
    (fun D hD hD9 W hDW hW => eq_bot_of_elemAbelian_normalizes hLn he hLc hidx hD hD9 hDW hW)

theorem kfactRankThreeStructure_of_core (hcore : KFactRankThreeCore) :
    KFactRankThreeStructure :=
  kfactRankThreeStructure_of_grp (k2Grp_of_core hcore)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
