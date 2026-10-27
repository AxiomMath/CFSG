module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Konvisser3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.GL3Rank
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113a

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem input31_6_holds : Input31_6 :=
  input31_6_of_three input31_3_three input31_GL3Rank_holds

theorem lemma104_iv_holds : Lemma104_ivStatement :=
  lemma104_iv_of_input31_6 input31_6_holds

theorem lemma113_ii_piece0_holds : Lemma113_ii_piece0Statement :=
  lemma113_ii_piece0_of_input31_6 input31_6_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
