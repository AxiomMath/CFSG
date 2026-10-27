module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertA5Inputs
public import Certificates.Certificate4123
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal

public section

namespace CFSG.QuasithinUnique.Bridge.Over

namespace CertA5

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127

theorem cert_check : cert.check RN.enc = true :=
  Certificates.certificate4123.1

theorem members_ok : memberOK cert cts = true :=
  Certificates.certificate4123.2.1

theorem mGens_even : ∀ g ∈ mGens, Equiv.Perm.sign g = 1 :=
  Certificates.certificate4123.2.2.1

theorem tGens_even : ∀ g ∈ tGens, Equiv.Perm.sign g = 1 :=
  Certificates.certificate4123.2.2.2

theorem card_alt : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem closure_mGens : Subgroup.closure {g | g ∈ mGens} = alternatingGroup (Fin 5) :=
  closure_eq_alt_of_cert cert cert_check mGens_even (by rw [card_alt]; rfl)

abbrev D : Subgroup (Perm (Fin 5)) := Subgroup.closure {g | g ∈ tGens}

theorem D_le : D ≤ alternatingGroup (Fin 5) := by
  rw [Subgroup.closure_le]
  intro g hg
  exact Equiv.Perm.mem_alternatingGroup.2 (tGens_even g hg)

theorem isSylow_D : IsSylowTwoOf (D.subgroupOf (alternatingGroup (Fin 5))) ⊤ :=
  isSylow_of_cert cert closure_mGens cert_check (k := 2) (m := 15) (by decide) (by decide)
    (by decide)

theorem overgroups : Overgroups ↥(alternatingGroup (Fin 5)) :=
  Overgroups.of_sylow _ isSylow_D fun Y hY hne =>
    (overgroups_charTwo cert cts closure_mGens D_le cert_check members_ok Y hY).resolve_left hne

end CertA5

end CFSG.QuasithinUnique.Bridge.Over
