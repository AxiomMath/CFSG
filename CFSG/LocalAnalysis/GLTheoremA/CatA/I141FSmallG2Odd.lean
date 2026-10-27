module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416TConv
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Converse


theorem i141f_g2odd_of_catDistinct (hD : CatDistinctAt) : I141RankG2Odd := by
  intro p hp hp2 Γ _ _ L A hcat hA hInn hcard
  obtain ⟨lab, hlab, hM⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_markedModel_centerQuot hInn.2
  have hch : IsChevSimple 2 (PSimple p L) := chev2MarkedConverse_holds _ ⟨lab, hlab, hM⟩
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | G2 q =>
      have hq : q.p ≠ 2 := hi
      exact hq (hD.g2_chev2 (PSimple p L) q hv ⟨e⟩ hch)
    | _ => exact absurd hi (by simp [onLie])
  | _ => exact absurd hi (by simp [onLie])

end Converse

section Certs


theorem i141RankG2Odd_holds
    : I141RankG2Odd := i141f_g2odd_of_catDistinct catDistinctAt_holds

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
