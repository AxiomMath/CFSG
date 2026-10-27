module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafOdd4
public import CFSG.LieType.TwoRank.StatedModels

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Open

theorem o3Facts_holds : O3Facts := by
  intro ι F _ _ _ h2 hι H
  have hF : ringChar F ≠ 2 := by
    intro h
    apply h2
    have h0 := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at h0
    exact_mod_cast h0
  refine ⟨fun E hE => ?_, fun E hE h16 h hhE hh => ?_⟩
  · haveI := isElemAbelian_iff_isElementaryAbelian.mp hE
    exact CFSG.LieType.TwoRank.card_le_sixteen_of_isElementaryAbelian_statedProj hF hι E
  · haveI := isElemAbelian_iff_isElementaryAbelian.mp hE
    exact CFSG.LieType.TwoRank.trace_eq_zero_of_card_eq_sixteen_statedProj hF hι E h16 hhE hh

end CFSG.SectionRank.QTK.Insp443

end
