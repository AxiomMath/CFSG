module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.Lemma121

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem kFact64iiI121_of_weakClosureInner (h : Stroth.WeakClosure.KFactWeakClosureInner) :
    KFact64iiI121 := by
  intro p hp hp3 K _ _ hs hna hcat P hcomm hrk A hAP hAc hN
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hcomm
  obtain ⟨g, hgP, hgne⟩ := h p hp (by omega) K hs hna hcat P hcomm hrk A hAP hAc
  exact hgne (SmallRank.map_conj_eq_of_normalizer_le P hAP hgP hN)

section Certified


theorem kFact64iiI121_holds : KFact64iiI121 :=
  kFact64iiI121_of_weakClosureInner SmallRank.kFactWeakClosureInner_holds

theorem kFact64iiL_of_outer (hOuter : KFact64iiOuterSylow) : KFact64iiL :=
  kFact64iiL_of_inputs hOuter kFact64iiI121_holds

theorem kFact64iiNPC_of_outer (hOuter : KFact64iiOuterSylow) (hNPC : KFact64iiOuterNPC) :
    KFact64iiNPC :=
  kFact64iiNPC_of_inputs hOuter kFact64iiI121_holds hNPC

end Certified

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
