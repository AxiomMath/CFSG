module

public import Certificates.Certificate23004
public import Certificates.Certificate23005

public section

namespace CFSG.ComponentClassification.GSThmB.CovHS

theorem covHS_klein_check : kleinCheck = true :=
  Certificates.certificate23004

theorem covHS_outer_check : outerCheck = true :=
  Certificates.certificate23005

end CFSG.ComponentClassification.GSThmB.CovHS
