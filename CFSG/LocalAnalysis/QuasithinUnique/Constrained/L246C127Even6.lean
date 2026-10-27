module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even6Inputs
public import Certificates.Certificate4130
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public meta import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCT
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCT
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.Code.Weights
public meta import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public meta import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public meta import CFSG.Quasithin.Background.A3Structure36A
public meta import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BAction
public meta import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BBase
public meta import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public meta import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public meta import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public meta import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public meta import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public meta import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public meta import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public meta import CFSG.Quasithin.Background.A3Structure36BStarBase
public meta import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public meta import CFSG.Quasithin.Background.A3Structure38Part3
public meta import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public meta import CFSG.Quasithin.Background.B1MoreNineG
public meta import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public meta import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public meta import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public meta import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public meta import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public meta import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public meta import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public meta import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.L246C127

namespace Even6

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem cert_check : cert.check RN.enc = true :=
  Certificates.certificate4130.1

theorem members_ok : memberOK cert cts = true :=
  Certificates.certificate4130.2.1

theorem mGens_even : ∀ g ∈ mGens, Equiv.Perm.sign g = 1 :=
  Certificates.certificate4130.2.2.1

theorem tGens_even : ∀ g ∈ tGens, Equiv.Perm.sign g = 1 :=
  Certificates.certificate4130.2.2.2

theorem card_alt : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem closure_mGens : Subgroup.closure {g | g ∈ mGens} = alternatingGroup (Fin 6) :=
  closure_eq_alt_of_cert cert cert_check mGens_even (by rw [card_alt]; rfl)

abbrev D : Subgroup (Perm (Fin 6)) := Subgroup.closure {g | g ∈ tGens}

theorem D_le : D ≤ alternatingGroup (Fin 6) := by
  rw [Subgroup.closure_le]
  intro g hg
  exact Equiv.Perm.mem_alternatingGroup.2 (tGens_even g hg)

theorem isSylow_D : IsSylowTwoOf (D.subgroupOf (alternatingGroup (Fin 6))) ⊤ :=
  isSylow_of_cert cert closure_mGens cert_check (k := 3) (m := 45) (by decide) (by decide)
    (by decide)

theorem overgroups (Y : Subgroup ↥(alternatingGroup (Fin 6)))
    (hDY : D.subgroupOf (alternatingGroup (Fin 6)) ≤ Y) : Y = ⊤ ∨ CharTwo Y :=
  overgroups_charTwo cert cts closure_mGens D_le cert_check members_ok Y hDY

end Even6

end CFSG.QuasithinUnique.L246C127
