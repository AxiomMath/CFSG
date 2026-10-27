module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusSuzukiModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428SuzukiGroupEq
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallerRecognitionDischarge
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.SteinbergBSDihedralPair
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.ComponentClassification.OuterAutomorphisms

theorem no_order_three_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ¬ ∃ η : MulAut G,
      η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived G ∧
        η ^ 3 = 1 ∧ η ≠ 1) :
    ¬ ∃ η : MulAut H,
      η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived H ∧
        η ^ 3 = 1 ∧ η ≠ 1 := by
  rintro ⟨η, hη, hη3, hη1⟩
  refine h ⟨MulAut.congr e.symm η, ?_, ?_, ?_⟩
  · exact (mem_innAutDerived_congr e.symm).2 hη
  · rw [← map_pow, hη3, map_one]
  · intro hconj
    apply hη1
    have h2 : MulAut.congr e (MulAut.congr e.symm η) = η := by
      ext x
      simp [MulAut.congr_apply]
    calc η = MulAut.congr e (MulAut.congr e.symm η) := h2.symm
      _ = MulAut.congr e 1 := by rw [hconj]
      _ = 1 := map_one _

noncomputable def suzukiCatalogueEquiv (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    CFSG.Blueprint.suzukiGroup m (GaloisField 2 (2 * m + 1)) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩).Group :=
  (MulEquiv.subgroupCongr (blueprint_suzukiGroup_eq_tauCeti m)).trans
    ((CFSG.BenderSuzuki.Catalog.suzukiGroupEquiv m).trans
      (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup (m := m) hv).symm)

theorem suzuki_catalogue_no_order_three
    (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    ¬ ∃ η : MulAut (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩).Group,
      η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived _ ∧
        η ^ 3 = 1 ∧ η ≠ 1 := by
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  exact no_order_three_of_mulEquiv (suzukiCatalogueEquiv m hv)
    (suzukiModel_no_order_three (m := m) hm1)

end CFSG.LocalAnalysis.GLTheoremA
