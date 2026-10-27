module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Lattice
public import Certificates.Certificate4058
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertL32Inputs
public import Certificates.Certificate4124
public import Certificates.Certificate4082
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal

public section

namespace CFSG.QuasithinUnique.Bridge.Over

namespace CertL32

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem cert_check : cert.check RN.enc = true :=
  Certificates.certificate4124.1

theorem members_ok : memberOK cert cts = true :=
  Certificates.certificate4124.2.1

theorem closure_mGens : Subgroup.closure {g | g ∈ mGens} = Seven.Z 8 := rfl

abbrev D : Subgroup (Perm (Fin 7)) := Subgroup.closure {g | g ∈ tGens}

theorem tle_ok : cert.tleOK RN.enc = true :=
  Certificates.certificate4124.2.2

theorem D_le : D ≤ Seven.Z 8 := by
  rw [← closure_mGens]
  exact cert.t_le_m (rawIsEnc 7) (cert.closedOK_of_check cert_check) tle_ok

theorem isSylow_D : IsSylowTwoOf (D.subgroupOf (Seven.Z 8)) ⊤ :=
  isSylow_of_cert cert closure_mGens cert_check (k := 3) (m := 21) (by decide) (by decide)
    (by decide)

theorem overgroups : Overgroups ↥(Seven.Z 8) :=
  Overgroups.of_sylow _ isSylow_D fun Y hY hne =>
    (overgroups_charTwo cert cts closure_mGens D_le cert_check members_ok Y hY).resolve_left hne

theorem overgroups_sl : Overgroups (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  Overgroups.of_mulEquiv Seven.z8Equiv.symm overgroups

end CertL32

end CFSG.QuasithinUnique.Bridge.Over
