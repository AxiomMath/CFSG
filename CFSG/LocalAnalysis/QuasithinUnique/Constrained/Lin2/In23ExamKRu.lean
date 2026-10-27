module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRuInputs
public import Certificates.Certificate4076
public import Certificates.Certificate4143
public import Certificates.Certificate3172
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

open CFSG.Open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem ru_fusionCert :
    FusionCert.FusionCertS ruData.n ruB ruTa ruTb ruProg ruQp ruEnum.1 ruEnum.2.1 ruEnum.2.2 14
      ruZI ruWit ruGW :=
  Certificates.certificate4076

theorem ru_group_strongCard : StrongCard ↥(J ruData) 14 := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have ha : tab ruData.n (a ruData) = ruTa.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a hF.toBaseFacts)]
    simp [ruTa]
  have hb : tab ruData.n (b ruData) = ruTb.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b hF.toBaseFacts)]
    simp [ruTb]
  have hcard0 : Nat.card (J ruData) = 145926144000 :=
    (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  have hcard : Nat.card (J ruData) = 2 ^ 14 * 8906625 := by
    rw [hcard0]; norm_num
  exact FusionCert.strongCard_of_fusionCertS (n := ruData.n) (B := ruB) (base_lt hF)
    (base_property hF) (a ruData) (b ruData) ruProg ru_valid ruQp ruEnum.1 ruEnum.2.1 ruEnum.2.2
    14 ruZI ruWit ruGW 8906625 hcard (by decide) (by
      rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
      exact ru_fusionCert)

theorem ru_native_strongCard' : StrongCard CFSG.Blueprint.NativeSporadic.Ru 14 := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  exact StrongCard.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.Ru) (Y := ↥(J ruData))
    (seedEquiv hF.toBaseFacts) ru_group_strongCard

theorem ru_native_strongCard : StrongCard (Carrier .Ru) 14 := by
  have h := ru_native_strongCard'
  exact h

end CFSG.QuasithinUnique.Lin2
