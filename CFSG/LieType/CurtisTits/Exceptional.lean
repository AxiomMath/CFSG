module

public import CFSG.LieType.CurtisTits.Minuscule
public import CFSG.LieType.CurtisTits.TwistedE6
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.LieType.CurtisTits

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny

universe w

variable (p f : ℕ) [Fact p.Prime]

theorem curtisTitsConclusion_e6 (hadm : StatedLieAdmissible .E6 0 p f) :
    CurtisTitsConclusion.{w} (e6Datum (GaloisField p f)) .E6 0 p f :=
  curtisTitsConclusion_e6_of_surjective p f hadm (e6Isogeny _) (e6Isogeny_surjective _)

theorem curtisTitsConclusion_e7 (hadm : StatedLieAdmissible .E7 0 p f) :
    CurtisTitsConclusion.{w} (e7Datum (GaloisField p f)) .E7 0 p f :=
  curtisTitsConclusion_e7_of_surjective p f hadm (e7Isogeny _) (e7Isogeny_surjective _)

theorem curtisTitsConclusion_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 p f) :
    CurtisTitsConclusion.{w} (twistedE6Datum p f) .twistedE6 0 p f :=
  curtisTitsConclusion_twistedE6_of_surjective p f hadm (twistedE6Isogeny p f hadm.2.1)
    (twistedE6Isogeny_surjective p f hadm.2.1) (twistedE6Isogeny_ne_one p f hadm.2.1)

end CFSG.LieType.CurtisTits
