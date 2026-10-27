module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22DataInputs
public import Certificates.Certificate4053
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

namespace M22Lat

open Equiv PermLat

theorem cert_check : cert.check RN.enc = true :=
  Certificates.certificate4053.1

theorem ext5_ok :
    diagExtOK (RN.enc : Perm (Fin 22) → RN 22) (RN.enc : Perm (Fin 5) → RN 5) 64
    p5Gens a5Gens 960 60 = true :=
  Certificates.certificate4053.2.1

theorem ext6_ok :
    diagExtOK (RN.enc : Perm (Fin 22) → RN 22) (RN.enc : Perm (Fin 6) → RN 6) 64
    l6Gens a6Gens 5760 360 = true :=
  Certificates.certificate4053.2.2.1

theorem perf5_ok :
    perfOK (RN.enc : Perm (Fin 22) → RN 22) p5Gens perf5 = true :=
  Certificates.certificate4053.2.2.2.1

theorem perf6_ok :
    perfOK (RN.enc : Perm (Fin 22) → RN 22) l6Gens perf6 = true :=
  Certificates.certificate4053.2.2.2.2.1

theorem incl5 :
    (List.range 6).all (fun j => cert.sizes.getD j 0 != 1920 ||
    p5Gens.all fun g => (elts (RN.enc : Perm (Fin 22) → RN 22) 64
      ((cert.tGens :: cert.lat).getD j [])).contains (RN.enc g)) = true :=
  Certificates.certificate4053.2.2.2.2.2.1

theorem incl6 :
    (List.range 6).all (fun j => cert.sizes.getD j 0 != 5760 ||
    l6Gens.all fun g => (elts (RN.enc : Perm (Fin 22) → RN 22) 64
      ((cert.tGens :: cert.lat).getD j [])).contains (RN.enc g)) = true :=
  Certificates.certificate4053.2.2.2.2.2.2

end M22Lat

end CFSG.QuasithinUnique.Vol2Native.A312L
