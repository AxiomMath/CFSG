module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKM24Inputs
public import Certificates.Certificate4072
public import Certificates.Certificate4075
public import Certificates.Certificate3017
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

open CFSG.Open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b card_M24)

theorem m24_fusionCert :
    FusionCert.FusionCertS 24 (List.range 24) m24ta.toArray m24tb.toArray m24Prog m24Qp m24Enum.1
      m24Enum.2.1 m24Enum.2.2 10 m24ZI m24Wit m24GW :=
  Certificates.certificate4072

theorem m24_strongCard : StrongCard ↥CFSG.Blueprint.NativeSporadic.M24 10 :=
  FusionCert.strongCard_of_fusionCertS (n := 24) (B := List.range 24)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m24a m24b m24Prog m24_valid m24Qp
    m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 m24ZI m24Wit m24GW 239085
    (by rw [card_M24]; norm_num) (by decide) (by
      rw [m24_tab_a, m24_tab_b]
      exact m24_fusionCert)

end CFSG.QuasithinUnique.Lin2
