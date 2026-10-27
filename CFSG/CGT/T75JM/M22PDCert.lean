module

public import CFSG.CGT.T75JM.M22PD
public import CFSG.CGT.T75JM.M22PresCert
public import Certificates.Certificate14989

public section

namespace CFSG.CGT.T75JM

open CFSG.Blueprint

theorem r22PDStatement_of_certificate :
    R22PDStatement := by
  intro H _ e hrel hK
  obtain ⟨hE, hθ⟩ := Certificates.certificate14989
  exact exists_mulEquiv_m22PD_of_relations e m22Facts_holds.2 hθ hE hrel hK

end CFSG.CGT.T75JM
