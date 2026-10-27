module

public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LieType.Steinberg.Adjoint.Presentation
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.Exceptional

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal CFSG.Blueprint.Chevalley

variable (p f : ℕ) [Fact p.Prime]

abbrev e6UniversalGroup : Type := ↥(e6Data_valid.minGroup (GaloisField p f))

abbrev e6UniversalDatum : UniversalRootDatum (e6UniversalGroup p f) := e6Datum (GaloisField p f)

abbrev e7UniversalGroup : Type := ↥(e7Data_valid.minGroup (GaloisField p f))

abbrev e7UniversalDatum : UniversalRootDatum (e7UniversalGroup p f) := e7Datum (GaloisField p f)

abbrev f4UniversalGroup : Type := ↥(adjointGroup .F4 (GaloisField p f))

abbrev f4UniversalDatum : UniversalRootDatum (f4UniversalGroup p f) :=
  CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField p f)

abbrev e8UniversalGroup : Type := ↥(adjointGroup .E8 (GaloisField p f))

abbrev e8UniversalDatum : UniversalRootDatum (e8UniversalGroup p f) :=
  CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField p f)

end CFSG.LieType.Steinberg.Exceptional
