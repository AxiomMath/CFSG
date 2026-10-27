module

public import CFSG.LocalAnalysis.RankThreeUC.K37HRCover
public import CFSG.RankThree.PartOne.KP.Fi22Unitary
public import CFSG.RankThree.PartOne.KP.UnitaryTorus
public import CFSG.Sporadic.Fi23.Fischer
public import CFSG.Sporadic.Fi24.ExtFi23

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartOne

theorem k37R_coverRankFour_fi22J :
    K37RCoverRankFour ↥CFSG.Sporadic.Fi22.J := by
  refine K37RCoverRankFour.of_centralizer_quotCenter (C := ↥CFSG.Fischer.T46) ?_
    CFSG.Sporadic.Fi22.commutator_T46 (a := CFSG.Sporadic.Fi22.a)
    CFSG.Sporadic.Fi22.orderOf_a (M := CFSG.Sporadic.Fi22.Ca)
    (fun m hm => CFSG.Sporadic.Fi22.mem_Ca.1 hm) CFSG.Sporadic.Fi22.caQuotEquiv
  intro Y _ _ f hf hk
  obtain ⟨U, hU, hUc⟩ := stated_psu6_central_cover
    (statedProjEquivT46.symm.toMonoidHom.comp f) (statedProjEquivT46.symm.surjective.comp hf)
    (by
      intro y hy
      apply hk
      rw [MonoidHom.mem_ker] at hy ⊢
      exact (MulEquiv.map_eq_one_iff statedProjEquivT46.symm).1 (by simpa using hy))
  exact ⟨U, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 U).mp hU, hUc⟩

theorem k37R_coverRankFour_fi23J :
    K37RCoverRankFour ↥CFSG.Sporadic.Fi23.J :=
  k37R_coverRankFour_fi22J.of_section_quotCenter CFSG.Sporadic.Fi22.commutator_eq_top
    (M := Subgroup.centralizer {CFSG.Sporadic.Fi23.d}) CFSG.Sporadic.Fi23.quotCenterEquiv

theorem k37R_coverRankFour_Fi22 :
    K37RCoverRankFour CFSG.Blueprint.NativeSporadic.Fi22 :=
  k37R_coverRankFour_fi22J.of_mulEquiv CFSG.Sporadic.Fi22.fi22EquivJ

theorem k37R_coverRankFour_Fi23 :
    K37RCoverRankFour CFSG.Blueprint.NativeSporadic.Fi23 :=
  k37R_coverRankFour_fi23J.of_mulEquiv CFSG.Sporadic.Fi23.fi23EquivJ

theorem k37R_coverRankFour_fi24J :
    K37RCoverRankFour ↥CFSG.Sporadic.Fi24.J := by
  have hC : K37RCoverRankFour ↥CFSG.Sporadic.Fi24.M :=
    k37R_coverRankFour_Fi23.of_mulEquiv CFSG.Sporadic.Fi24.fi23Equiv
  have hperf : commutator ↥CFSG.Sporadic.Fi24.M = ⊤ :=
    @k37R_commutator_eq_top_of_mulEquiv ↥CFSG.Sporadic.Fi24.M CFSG.Blueprint.NativeSporadic.Fi23
      inferInstance inferInstance CFSG.Sporadic.Fi24.fi23Equiv
      (@k37R_commutator_eq_top_of_mulEquiv CFSG.Blueprint.NativeSporadic.Fi23 ↥CFSG.Sporadic.Fi23.J
        inferInstance inferInstance CFSG.Sporadic.Fi23.fi23EquivJ CFSG.Sporadic.Fi23.commutator_J)
  exact hC.of_section (M := CFSG.Sporadic.Fi24.M) hperf (MonoidHom.id _) Function.surjective_id
    (by simp)

theorem k37R_coverRankFour_Fi24Prime :
    K37RCoverRankFour CFSG.Blueprint.NativeSporadic.Fi24prime :=
  k37R_coverRankFour_fi24J.of_mulEquiv CFSG.Sporadic.Fi24.fi24EquivJ

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
