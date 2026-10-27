module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHeInputs
public import Certificates.Certificate4073
public import Certificates.Certificate4141
public import Certificates.Certificate3168
public meta import CFSG.GroupTheory.PerfectResidualNodes
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.Quasithin.Background.A1cModuleCoprime
public meta import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3Structure312
public meta import CFSG.Quasithin.Background.OrderingMax
public meta import CFSG.Quasithin.Vol2.Ch1Local
public meta import CFSG.Sporadic.Schreier.J4SSylow
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public meta import CFSG.Walter.Defs
public meta import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.He
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem he_fusionCert :
    FusionCert.FusionCertS 8330 heB heTa heTb heProg heQp heEnum.1 heEnum.2.1 heEnum.2.2 10 heZI
      heWit heGW :=
  Certificates.certificate4073

theorem he_group_strongCard : StrongCard ↥J 10 := by
  have ha : tab 8330 (a : J) = heTa.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (a : J) rep_alpha]
    simp [heTa, orb]
  have hb : tab 8330 (b : J) = heTb.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (b : J) rep_beta]
    simp [heTb, orb]
  exact FusionCert.strongCard_of_fusionCertS (n := 8330) (B := heB) he_base_lt he_base_property
    (a : J) (b : J) heProg he_valid heQp heEnum.1 heEnum.2.1 heEnum.2.2 10 heZI heWit heGW 3935925
    (by rw [card_J]; norm_num) (by decide) (by
      rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
      exact he_fusionCert)

theorem he_native_strongCard' : StrongCard CFSG.Blueprint.NativeSporadic.He 10 :=
  StrongCard.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.He) (Y := ↥J) heEquivJ
    he_group_strongCard

theorem he_native_strongCard : StrongCard (Carrier .He) 10 := by
  have h := he_native_strongCard'
  exact h

end CFSG.QuasithinUnique.Lin2
