module

public import CFSG.LieType.Chevalley.RootOps.Poly
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

@[expose] def g2Reps : List (ℕ × ℕ × List Factor) := [
  (0, 1, [(1, 1, 4, 1), (1, 2, 8, -1), (1, 3, 3, -1), (2, 3, 7, 1)]),
  (0, 3, [(1, 1, 7, 1)]),
  (0, 4, []),
  (0, 7, []),
  (0, 8, []),
  (1, 0, [(1, 1, 4, -1), (2, 1, 8, 1), (3, 1, 3, 1), (3, 2, 7, 2)]),
  (1, 3, []),
  (1, 4, [(1, 1, 8, -2), (1, 2, 7, -3), (2, 1, 3, -3)]),
  (1, 7, []),
  (1, 8, [(1, 1, 3, 3)])]

@[expose] def g2Cover : List ℕ := [
  16, 4144, 8256, 12400, 16512, 20481, 24625, 28737, 32881, 36993]

end CFSG.LieType.Chevalley.RootOps
