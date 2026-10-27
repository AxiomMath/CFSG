module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public import CFSG.GH74.KGroups.U33
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public meta import CFSG.GH74.KGroups.U33
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33Inputs
public import Certificates.Certificate4125
public import Certificates.Certificate5133
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal

public section

namespace CFSG.QuasithinUnique.Bridge.Over

namespace CertU33

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127
  CFSG.Blueprint

theorem cert_check : cert.check RN.enc = true :=
  Certificates.certificate4125.1

theorem members_ok : memberOK cert cts = true :=
  Certificates.certificate4125.2.1

theorem closure_mGens :
    Subgroup.closure {g | g ∈ mGens} = CFSG.GH74.KGroups.U33.QP.originalSubgroup := by
  rw [CFSG.GH74.KGroups.U33.QP_closure]
  congr 1
  ext g
  simp [mGens]

abbrev D : Subgroup (Perm (Fin 28)) := Subgroup.closure {g | g ∈ tGens}

theorem tle_ok : cert.tleOK RN.enc = true :=
  Certificates.certificate4125.2.2

theorem D_le : D ≤ CFSG.GH74.KGroups.U33.QP.originalSubgroup := by
  rw [← closure_mGens]
  exact cert.t_le_m (rawIsEnc 28) (cert.closedOK_of_check cert_check) tle_ok

theorem isSylow_D :
    IsSylowTwoOf (D.subgroupOf CFSG.GH74.KGroups.U33.QP.originalSubgroup) ⊤ :=
  isSylow_of_cert cert closure_mGens cert_check (k := 5) (m := 189) (by decide) (by decide)
    (by decide)

theorem overgroups : Overgroups ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
  Overgroups.of_sylow _ isSylow_D fun Y hY hne =>
    (overgroups_charTwo cert cts closure_mGens D_le cert_check members_ok Y hY).resolve_left hne

theorem overgroups_of_lieModel {K : Type} [Group K] (h : LieModel K .PSU 3 3 1) : Overgroups K := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel h
  exact Overgroups.of_mulEquiv e.symm overgroups

end CertU33

end CFSG.QuasithinUnique.Bridge.Over
