module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadList
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3
public import CFSG.LieType.Simplicity.Classical
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadList
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadL33Inputs
public import Certificates.Certificate4056
public import Certificates.Certificate4145
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadical
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadical
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Background.A3Structure39Aut
public meta import CFSG.Quasithin.Background.A3Structure39Aut
public import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.QuasithinUnique.Unc25K1

theorem s3_hcenter :
    CenterOK s3Model.mul s3Model.one s3Model.elems :=
  Certificates.certificate4056.1

theorem s3_hodd :
    OddOK s3Model.mul s3Model.one 351 s3Model.elems s3Invs s3Ord4 :=
  Certificates.certificate4056.2.1

theorem s3_hquat :
    QuatAll s3Model.mul s3Model.one s3Model.elems s3Invs :=
  Certificates.certificate4056.2.2.1

theorem s3_hcore :
    CoreAll s3Model.mul s3Model.one s3Model.inv s3Model.elems s3Invs :=
  Certificates.certificate4056.2.2.2

theorem radData_of_stated_l33 {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .PSL 3 3 1) : RadData Y := by
  obtain ⟨e₀⟩ := psl33_equiv h
  let e : Y ≃* S3 := e₀.trans psl33EquivS3
  have hS : IsSimpleGroup Y := (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 3 1 h).2
  have hcard : Nat.card Y = 16 * 351 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_S3
  refine radData_of_listModel_equiv s3Model e hS (m := 351) (by decide) (by norm_num) hcard
    s3Invs s3Ord4 ?_ ?_ s3_hcenter s3_hodd s3_hquat s3_hcore
  · intro t
    rw [s3Invs, List.mem_filter, decide_eq_true_eq]
  · intro u
    rw [s3Ord4, List.mem_filter, decide_eq_true_eq]

end CFSG.QuasithinUnique.Fin253
