module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FP
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycCyc
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.OutCyc

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S3 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.StandardType


theorem outCyclicAt_of_odd
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutCyclicAt G p := by
  intro B x L A hS hK hchev hBN hAB
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hS.2.2
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hL
  have M₀ := Canonical.largeEvenMarking_markedModel
    (CFSG.StandardType.ChevTwo.ys08_holds (PQuot p L) hq hchev)
  by_cases hD : p = 3 ∧ catalogIs (PSimple p L) isD4any
  · obtain ⟨rfl, hcat⟩ := hD
    exact outCyc_D4_case B x L A hS hK hchev hcat hAB hBN M₀
  · exact outCyc_cyc_case hp hp2 B x L A hS hchev hD hAB hBN M₀

theorem outCyclicAt_holds
    {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : (p.Prime ∧ p ≠ 2) ∨ p ≤ 1) : OutCyclicAt G p := by
  rcases hp with ⟨hp, hp2⟩ | hp
  · exact outCyclicAt_of_odd hp hp2
  · exact outCyclicAt_of_le_one hp

end CFSG.LocalAnalysis.GLTheoremA.OutCyc

end
