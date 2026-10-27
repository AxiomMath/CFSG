module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input31
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma104c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec11Small

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem lemma103_holds : Lemma103Statement :=
  lemma103_of_input31_8 input31_8_holds isUniquenessTwoLocal_conj_holds

theorem lemma104_v_holds : Lemma104_vStatement :=
  lemma104_v_of_input31_8 input31_8_holds

theorem lemma104_vi_holds : Lemma104_viStatement :=
  lemma104_vi_of_lemma104_v lemma104_v_holds

theorem lemma113_i_holds : Lemma113_iStatement :=
  lemma113_i_of_104v lemma104_v_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
