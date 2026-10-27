module

public import Certificates.Certificate12044
public import Certificates.Certificate12045

public section

namespace CFSG.LieType.Multipliers.G24

theorem inv_check : invCheck = true :=
  Certificates.certificate12044.1

theorem rel_check : relCheck = true :=
  Certificates.certificate12044.2.1

theorem comm_check : commCheck = true :=
  Certificates.certificate12044.2.2.1

theorem root_check : rootCheck = true :=
  Certificates.certificate12044.2.2.2.1

theorem suz_check : suzCheck = true :=
  Certificates.certificate12044.2.2.2.2

theorem unit_check : unitCheck = true :=
  Certificates.certificate12045.1

theorem cover_check : coverCheck = true :=
  Certificates.certificate12045.2.1

theorem ker_check : kerCheck = true :=
  Certificates.certificate12045.2.2

end CFSG.LieType.Multipliers.G24
