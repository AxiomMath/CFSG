module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate4060
public import Certificates.Certificate4140
public import Certificates.Certificate3167
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

open CFSG.Open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_rankCert :
    RankCert.RankCertS hsData.n hsB (slpTabsA hsTa hsTb hsProg) hsQp 4 hsEnum.1 hsEnum.2.1
      hsEnum.2.2 9 :=
  Certificates.certificate4060

theorem hs_group_rank : RankCert.ElemAbelianLt (J hsData) 32 := by
  have hF : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts
  have ha : tab hsData.n (a hsData) = hsTa.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (a hsData) (rep_a hF.toBaseFacts)]
    simp [hsTa]
  have hb : tab hsData.n (b hsData) = hsTb.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (b hsData) (rep_b hF.toBaseFacts)]
    simp [hsTb]
  have hcard0 : Nat.card (J hsData) = 44352000 :=
    (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.HS.card_HS
  have hcard : Nat.card (J hsData) = 2 ^ 9 * 86625 := by
    rw [hcard0]; norm_num
  have h := RankCert.card_lt_of_baseEnumS (n := hsData.n) (Γ := J hsData) (B := hsB)
    (base_lt hF) (base_property hF) (a hsData) (b hsData) hsProg hs_valid hsQp 4 hsEnum.1
    hsEnum.2.1 hsEnum.2.2 9 86625 hcard (by decide) (by
      rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
      exact hs_rankCert)
  intro E hE
  have := h E hE
  norm_num at this
  exact this

theorem hs_native_rank' : RankCert.ElemAbelianLt CFSG.Blueprint.NativeSporadic.HS 32 := by
  have hF : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts
  exact RankCert.ElemAbelianLt.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.HS)
    (Y := ↥(J hsData)) (seedEquiv hF.toBaseFacts) hs_group_rank

theorem hs_native_rank : RankCert.ElemAbelianLt (Carrier .HS) 32 := by
  have h := hs_native_rank'
  exact h

end CFSG.QuasithinUnique.Lin2
