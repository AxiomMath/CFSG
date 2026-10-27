module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M22Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Two
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.M22
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M22Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Fix
public meta import CFSG.Sporadic.Mathieu.M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M22Inputs
public import Certificates.Certificate4078
public import Certificates.Certificate4065
public import Certificates.Certificate3029
public import Certificates.Certificate3157
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

namespace CFSG.QuasithinUnique.A5.Kc3M22

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six CFSG.QuasithinUnique.Unc25G2.M2x
  CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.A5.Kc3M22Data

theorem isEnc : IsEnc enc :=
  ⟨RN.enc_inj.comp Subtype.val_injective, fun _ _ => RN.enc_mul _ _, RN.enc_one⟩

theorem hexad_core : hexad.coreCheckT gR 443520 = true :=
  Certificates.certificate4078.1

theorem duad_core : duad.coreCheckT gR 443520 = true :=
  Certificates.certificate4078.2.1

theorem hexad_A : hexad.hypACheck gR = true :=
  Certificates.certificate4078.2.2.1

theorem duad_A : duad.hypACheck gR = true :=
  Certificates.certificate4078.2.2.2

theorem card_m22 : Nat.card ↥NativeSporadic.M22 = 443520 := CFSG.Sporadic.Schreier.m22_card

theorem locClass_m22 : LocClass ↥NativeSporadic.M22 := by
  obtain ⟨E₁, N₁, hs₁⟩ := hexad.exists_soundT isEnc m22a m22b 443520 card_m22 hexad_core
  obtain ⟨E₂, N₂, hs₂⟩ := duad.exists_soundT isEnc m22a m22b 443520 card_m22 duad_core
  refine locClass_of_twoE twoE_M22 ⟨hs₁.comm, hs₁.sq⟩ hs₁.cardE ⟨hs₂.comm, hs₂.sq⟩ hs₂.cardE ?_
    (hs₁.hypA isEnc hexad_A) (hs₂.hypA isEnc duad_A)
  rw [← hs₁.hN, hs₁.cardN, ← hs₂.hN, hs₂.cardN]
  decide

end CFSG.QuasithinUnique.A5.Kc3M22

namespace CFSG.QuasithinUnique.A5

open CFSG.Blueprint

theorem kc3LocalFor_m22 : Kc3LocalFor (Kc3Spor .M22) := by
  intro X _ _ ⟨e⟩
  exact kc3LocalData_of_locClass (LocClass.of_equiv e Kc3M22.locClass_m22)

end CFSG.QuasithinUnique.A5
