module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Core
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Dict

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (fieldFactor4 mem_range_conj_of_fieldFactor4_eq_one)

section Row25


theorem i91U48At_holds (G : Type) [Group G] [Finite G] : I91U48At G := by
  intro X L b hL hcat hFO
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hFO.1
  have hcatP := catalogIs_psimple hL hcat
  obtain ⟨hγ3, hγ1⟩ := dict_outer hcatP hFO (psModel hL hcat) (indAut (lModel hcat) b hb)
    (indAut_psModel hL hcat b hb)
  have hff : fieldFactor4 (indAut (lModel hcat) b hb) ≠ 1 := fun h =>
    hγ1 (mem_range_conj_of_fieldFactor4_eq_one h)
  obtain ⟨hcatFix, hcard⟩ := catalogIs_fixSub hγ3 hff
  refine ⟨(catalogIs_congr (centEquiv (lModel hcat) b hb)).2 hcatFix, ?_⟩
  unfold centCard2
  rw [card_fixedPoints hL hcat hb, hcard]
  exact twoPart_25920

end Row25

end CFSG.LocalAnalysis.GLTheoremA
