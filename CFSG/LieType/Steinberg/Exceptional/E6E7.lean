module

public import CFSG.LieType.Steinberg.Presentation
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.LieType.Universal

universe u w

variable (k : Type u) [Field k]

theorem e6_presentationA :
    PresentationA.{0, u, w} (RootSystem.ofCartan (e6Datum k).isFiniteType (e6Datum k).divisible)
      (e6Datum k).rootGroup :=
  presentationA_of (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k)

theorem e6_steinbergPresentation : (e6Datum k).SteinbergPresentation.{u, w} :=
  steinbergPresentation_of_extras (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k)

theorem e7_presentationA :
    PresentationA.{0, u, w} (RootSystem.ofCartan (e7Datum k).isFiniteType (e7Datum k).divisible)
      (e7Datum k).rootGroup :=
  presentationA_of (e7Datum_isCTGroupDatum k) (e7Datum_steinbergExtras k)

theorem e7_steinbergPresentation : (e7Datum k).SteinbergPresentation.{u, w} :=
  steinbergPresentation_of_extras (e7Datum_isCTGroupDatum k) (e7Datum_steinbergExtras k)

end CFSG.LieType.Steinberg.Minuscule
