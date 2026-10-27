module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyCoreThreeBCert
public import Certificates.Certificate5220

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore

theorem lyThreeBOrder_thm :
    LyThreeBOrder := by
  obtain ⟨_, h⟩ := Certificates.certificate5220
  exact lyThreeBOrder_of_J h

theorem lyCentralizerCore_thm :
    LyCentralizerCore :=
  lyCentralizerCore_of_threeBOrder lyThreeBOrder_thm

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore
