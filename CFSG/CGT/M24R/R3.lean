module

public import CFSG.CGT.M24R.R3Main
public import Certificates.Certificate21194

public section

namespace CFSG.CGT.M24R


theorem r3Facts_of_certificate : R3.R3Facts := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Certificates.certificate21194
  exact ⟨h1, h2, h3, h4, h5⟩

theorem r3Statement : R3Statement :=
  R3.r3Statement_of_facts r3Facts_of_certificate

end CFSG.CGT.M24R
