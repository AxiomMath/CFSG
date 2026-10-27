module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.LineStab
public import Certificates.Certificate753502

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier


noncomputable def alphaP : Pv ≃* Pv := Classical.choose Certificates.certificate753502

theorem alphaP_a0 : alphaP ⟨a0, a0_mem⟩ = pvEval alphaWordA :=
  (Classical.choose_spec Certificates.certificate753502).1

theorem alphaP_a1 : alphaP ⟨a1, a1_mem⟩ = ⟨a1, a1_mem⟩ :=
  (Classical.choose_spec Certificates.certificate753502).2

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
