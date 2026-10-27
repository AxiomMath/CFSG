module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinJ2A
public import Certificates.Certificate55106

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinJ2

open Subgroup CFSG.Sporadic.Schreier

theorem klein {x : Equiv.Perm (Fin 315)} (hx : x ∈ j2P)
    (ho : orderOf x = 3) : ∃ u₁ ∈ j2P, ∃ u₂ ∈ j2P, KleinWit x u₁ u₂ :=
  Certificates.certificate55106.1 x hx ho

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinJ2
