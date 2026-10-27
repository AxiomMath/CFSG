module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies
public import CFSG.HardMathSupport.Solomon.Coordinator.SporCover
public import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models
public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsU43
import CFSG.HardMathSupport.Lang.E6Descent.RankB3

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.RankThree.PartTwo.Sec4 (IsTripleCover)
open CFSG.LocalAnalysis.RankThreeTheoremC (HasLiftableTriple)

theorem threeNineThreeCoverRank_holds :
    ThreeNineThreeCoverRank := by
  intro K _ _ hKq hcov
  have hq' : CFSG.Open.IsQuasisimple K := ⟨Group.isPerfect_def.mp hKq.1, hKq.2.1⟩
  rcases hcov with ⟨hZ, ⟨e⟩⟩ | ⟨Y, _, hm, hZ, ⟨e⟩⟩ | ⟨Y, _, hm, hZ, ⟨e⟩⟩ | ⟨Y, _, hm, hZ, ⟨e⟩⟩
  ·
    obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
    exact CFSG.HardMathSupport.Solomon.Coordinator.sporCover_McL_pRank_ge_four K hKq.1 hZ
      ⟨e.trans ψ⟩
  ·
    obtain ⟨f⟩ := CFSG.HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_X₀_of_lieModel
      (Or.inl ⟨by decide, hm⟩)
    exact CFSG.LocalAnalysis.RankThreeTheoremC.U43Lift.hasLiftableTriple_X₀.four_le_pRank_of_cover
      (e.trans f) (by rw [hZ])
  ·
    obtain ⟨f⟩ := CFSG.HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_openOmega_of_lieModel
      (Or.inl ⟨by decide, hm⟩)
    have hle := CFSG.HardMathSupport.Timmesfeld.LieRank.O7.pRank_quotient_le_of_cover_O7 hq'
      (e.trans f) (by rw [hZ]) (by rw [hZ]; norm_num)
    obtain ⟨A, hA, hAc⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_elemAbelian_card_of_equiv
      (F := ZMod 3) (by simp) (e.trans f)
    have h5 : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hA hAc
    omega
  ·
    obtain ⟨f⟩ :=
      CFSG.HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_adjointGroup_G2_of_lieModel
        (Or.inr (Or.inl ⟨rfl, by decide, hm⟩))
    have hT : HasLiftableTriple Y := HasLiftableTriple.of_mulEquiv f.symm
      CFSG.LocalAnalysis.RankThreeTheoremC.G2Lift.hasLiftableTriple_adjointG2
    exact hT.four_le_pRank_of_cover e (by rw [hZ])

end CFSG.LocalAnalysis.AGL81I.Section3
