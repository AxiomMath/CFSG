module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRankLie
import CFSG.LocalAnalysis.GL83PartI.I_24_3.List
import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListLie
import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank

open CFSG.Assembly.LowTwoRank
open CFSG.Open (GriessAllModelsStatement)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (center_dvd_table)
open GL83.I243.CoverList (isQuasisimple_of_open false_of_cyclic card_center_dvd_alternating
  card_center_dvd_sporadic sporadicMultiplierOrder_dvd_twelve exists_lieModel_spec
  eq_three_of_dvd_twelve)

theorem schurMultiplierRankFact_of_tables (hGA : GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    SchurMultiplierRankFact := by
  intro p hp hp5 L _ _ hq ⟨i, ⟨e⟩⟩ hpZ
  have hp2 : p ≠ 2 := by omega
  have hq' := isQuasisimple_of_open hq
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  have hp12 : ¬ p ∣ 12 := fun h => by have := eq_three_of_dvd_twelve hp hp2 h; omega
  cases i with
  | cyclic r hr => exact (false_of_cyclic hq' e).elim
  | alternating n hn =>
    exfalso
    have h := hpZ.trans (card_center_dvd_alternating hAlt hq' hn e)
    split_ifs at h <;> exact hp12 (h.trans (by norm_num))
  | sporadic s =>
    exact (hp12 (hpZ.trans ((card_center_dvd_sporadic hSpor hq' e).trans
      (sporadicMultiplierOrder_dvd_twelve s)))).elim
  | lie d =>
    obtain ⟨t, n, r, f, hm, -, -, -, -⟩ := exists_lieModel_spec d
    have h := hpZ.trans (center_dvd_table hGA hq' e hm)
    obtain ⟨ht, ha⟩ := dvd_first_generic_of_five_le hp hp5 hm.1 h
    have hmK := CFSG.Models.LieModel.of_mulEquiv e.symm hm
    have hcl : StatedClassicalModel (L ⧸ Subgroup.center L) t n r f := by
      rcases hmK.2 with hcl | ⟨hn0, -⟩
      · exact hcl
      · exfalso
        have hn2 : 2 ≤ n := by
          rcases ht with rfl | rfl
          · exact hm.1.2.2.1
          · have := hm.1.2.2.1
            omega
        omega
    exact four_le_pRank_of_classical hGA hperf hp hp5 hpZ hcl ht ha

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank
