module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma102
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma104b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec9Remarks

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem sec10Fails_conj_holds : Sec10Fails_conjStatement :=
  sec10Fails_conj_of isUniquenessTwoLocal_conj_holds

theorem lemma104_iv_of_input31_6 (h31 : Input31_6) : Lemma104_ivStatement :=
  lemma104_iv_of lemma102_holds h31 isUniquenessTwoLocal_conj_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
