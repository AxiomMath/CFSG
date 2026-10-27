module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinReduce
public import CFSG.Sporadic.Schreier.Co3Sp6
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridge
public import CFSG.Blueprint.SourceClassicalTransport
public import Certificates.Certificate320203
public import Certificates.Certificate320204

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.Monster.B.Co2 CFSG.Open CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.OmegaEight
  CFSG.Blueprint.EvenSource

theorem sp6_noQ16 :
    NoQ16 ↥co3X36 :=
  Certificates.certificate320203

theorem om8_noQ16 :
    NoQ16 ↥omegaT :=
  Certificates.certificate320204

theorem noQ16E4_holds :
    NoQ16E4 := by
  intro Q _ hQ
  rcases hQ with hQ | hQ
  · obtain ⟨e⟩ := nonempty_mulEquiv_of_statedClassicalModel
      (hQ.statedClassicalModel (by decide)) co3X36_classicalModel
    exact NoQ16.of_injective e.toMonoidHom e.injective sp6_noQ16
  · obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hQ
    exact NoQ16.of_injective e.toMonoidHom e.injective om8_noQ16

end CFSG.CGT.PushingUpLit.SolKNA.R4
