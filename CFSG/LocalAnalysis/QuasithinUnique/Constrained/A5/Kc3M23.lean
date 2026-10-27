module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M23Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Two
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM23
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Schreier.M23
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M23Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Fix
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate4047
public import Certificates.Certificate41
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M23Inputs
public import Certificates.Certificate4074
public import Certificates.Certificate2197
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public meta import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cover
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.A3StructureBasic
public meta import CFSG.Quasithin.Background.B1Basic
public meta import CFSG.Quasithin.Background.C1GNInputs
public meta import CFSG.Quasithin.Background.C1GNNotation
public meta import CFSG.Quasithin.EmptyFaithful.QTKELocal
public meta import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public meta import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.A5.Kc3M23

open CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six CFSG.QuasithinUnique.Unc25G2.M2x
  CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.A5.Kc3M23Data

theorem isEnc : IsEnc enc :=
  ⟨RN.enc_inj.comp Subtype.val_injective, fun _ _ => RN.enc_mul _ _, RN.enc_one⟩

theorem heptad_core : heptad.coreCheckT gR 10200960 = true :=
  Certificates.certificate4074.1

theorem scalar_core : scalar.coreCheckT gR 10200960 = true :=
  Certificates.certificate4074.2.1

theorem heptad_A : heptad.hypACheck gR = true :=
  Certificates.certificate4074.2.2.1

theorem scalar_A : scalar.hypACheck gR = true :=
  Certificates.certificate4074.2.2.2

theorem card_m23 : Nat.card ↥NativeSporadic.M23 = 10200960 := CFSG.Sporadic.Schreier.m23_card

theorem locClass_m23 : LocClass ↥NativeSporadic.M23 := by
  obtain ⟨E₁, N₁, hs₁⟩ := heptad.exists_soundT isEnc m23a m23b 10200960 card_m23 heptad_core
  obtain ⟨E₂, N₂, hs₂⟩ := scalar.exists_soundT isEnc m23a m23b 10200960 card_m23 scalar_core
  refine locClass_of_twoE twoE_M23 ⟨hs₁.comm, hs₁.sq⟩ hs₁.cardE ⟨hs₂.comm, hs₂.sq⟩ hs₂.cardE ?_
    (hs₁.hypA isEnc heptad_A) (hs₂.hypA isEnc scalar_A)
  rw [← hs₁.hN, hs₁.cardN, ← hs₂.hN, hs₂.cardN]
  decide

end CFSG.QuasithinUnique.A5.Kc3M23

namespace CFSG.QuasithinUnique.A5

open CFSG.Blueprint

theorem kc3LocalFor_m23 : Kc3LocalFor (Kc3Spor .M23) := by
  intro X _ _ ⟨e⟩
  exact kc3LocalData_of_locClass (LocClass.of_equiv e Kc3M23.locClass_m23)

end CFSG.QuasithinUnique.A5
