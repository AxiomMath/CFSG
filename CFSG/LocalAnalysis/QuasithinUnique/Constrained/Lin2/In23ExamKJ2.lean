module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public import Certificates.Certificate4131
public import Certificates.Certificate4142
public import Certificates.Certificate3139
public meta import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public meta import CFSG.Quasithin.Background.A3Structure312
public meta import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Background.OrderingMax
public meta import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.Ch1Local
public meta import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.J4SSylow
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public meta import CFSG.Walter.Defs
public import Certificates.Certificate8026Base
public meta import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.J2

theorem j2_rankCert :
    RankCert.RankCertS 315 (List.range 315)
      (slpTabsA CFSG.QuasithinUnique.K1.SporadicPerm.j2ta.toArray
        CFSG.QuasithinUnique.K1.SporadicPerm.j2tb.toArray
        CFSG.QuasithinUnique.K1.SporadicPerm.j2Prog)
      CFSG.QuasithinUnique.K1.SporadicPerm.j2Qp 4
      CFSG.QuasithinUnique.K1.SporadicPerm.j2Enum.1
      CFSG.QuasithinUnique.K1.SporadicPerm.j2Enum.2.1
      CFSG.QuasithinUnique.K1.SporadicPerm.j2Enum.2.2 7 :=
  Certificates.certificate4131

theorem j2_group_rank : RankCert.ElemAbelianLt J 32 := by
  have h := RankCert.card_lt_of_baseEnumS (n := 315) (Γ := J) (B := List.range 315)
    (fun b hb => List.mem_range.mp hb) base_of_faithful (a : J) (b : J)
    CFSG.QuasithinUnique.K1.SporadicPerm.j2Prog
    CFSG.QuasithinUnique.K1.SporadicPerm.j2_valid
    CFSG.QuasithinUnique.K1.SporadicPerm.j2Qp 4
    CFSG.QuasithinUnique.K1.SporadicPerm.j2Enum.1
    CFSG.QuasithinUnique.K1.SporadicPerm.j2Enum.2.1
    CFSG.QuasithinUnique.K1.SporadicPerm.j2Enum.2.2 7 4725
    (by rw [card_J]; norm_num) (by decide) (by
      rw [CFSG.QuasithinUnique.K1.SporadicPerm.j2_tab_a,
        CFSG.QuasithinUnique.K1.SporadicPerm.j2_tab_b]
      exact j2_rankCert)
  intro E hE
  have := h E hE
  norm_num at this
  exact this

theorem j2_native_rank' : RankCert.ElemAbelianLt CFSG.Blueprint.NativeSporadic.J2 32 :=
  RankCert.ElemAbelianLt.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.J2) (Y := ↥J)
    CFSG.Sporadic.Bridge.J2.nativeEquiv j2_group_rank

theorem j2_native_rank : RankCert.ElemAbelianLt (NativeSporadic.Carrier .J2) 32 := by
  have h := j2_native_rank'
  exact h

end CFSG.QuasithinUnique.Lin2
