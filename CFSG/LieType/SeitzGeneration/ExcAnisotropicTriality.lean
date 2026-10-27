module

public import CFSG.LieType.SeitzGeneration.ExtSeitzFamily
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.RankThree.PartOne.CTP.SeitzFineD4
public import CFSG.RankThree.PartOne.SEITZ3.D4Assembly
public import CFSG.RankThree.PartOne.SEITZ7.D4Final
public import CFSG.RankThree.PartOne.D4RC.CentN
public import CFSG.RankThree.PartOne.D4RC.Phi6
public import CFSG.Goldschmidt.Final
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP TauCeti

section Even


theorem extSeitzAtInnerFor_trialityD4_even (hgold : CFSG.Goldschmidt.TopStatement)
    {q : PrimePower} (hq : q.p = 2) :
    ExtSeitzAtInnerFor (.trialityD4 q) fun _ => True := by
  have hBig : SEITZ3.Max3D4A1A1Big := SEITZ7.max3D4A1A1Big_of_top hgold
  have hPhi : SEITZ3.Exc3D4NonsplitPhi3Phi6 :=
    D4RC.exc3D4NonsplitPhi3Phi6_of_phi6 D4RC.rc6_max3D4CentN6
  exact extSeitzAtInnerFor_union (P₁ := fun p => p ∣ q.card - 1) (P₂ := fun p => ¬ p ∣ q.card - 1)
    (fun p _ _ _ => by by_cases h : p ∣ q.card - 1; exacts [Or.inl h, Or.inr h])
    (extSeitzAtInnerFor_trialityD4_split hq)
    (SEITZ3.exc3D4Nonsplit_of_narrow ⟨hBig, hPhi⟩ q hq)

theorem seitzExcAnisotropicForAt_triality_even (hgold : CFSG.Goldschmidt.TopStatement) :
    SeitzExcAnisotropicForAt IsTrialityIndex fun d p =>
      ∃ q : PrimePower, d = .trialityD4 q ∧ 5 ≤ p ∧ q.p = 2 :=
  seitzExcAnisotropicForAt_family (c := LieTypeIndex.trialityD4) (P := fun q _ => q.p = 2)
    (fun _ hv => finite_isSimpleGroup_cat_trialityD4 hv)
    fun _ K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hin =>
      extSeitzAtInnerFor_trialityD4_even hgold hP K hnab hiso p hp hp5 hpd trivial E hE hcard hin

end Even

@[expose] def SeitzExcAnisotropicTrialityOdd : Prop :=
  SeitzExcAnisotropicForAt IsTrialityIndex fun d p =>
    5 ≤ p ∧ ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2

@[expose] def SeitzExcAnisotropicTrialityThree : Prop :=
  SeitzExcAnisotropicForAt IsTrialityIndex PrimeRange.three

section Assembly


theorem seitzExcAnisotropicFor_triality_of_residuals (hgold : CFSG.Goldschmidt.TopStatement)
    (hodd : SeitzExcAnisotropicTrialityOdd) (h3 : SeitzExcAnisotropicTrialityThree) :
    SeitzExcAnisotropicTriality :=
  SeitzExcAnisotropicFor.of_three_geFive h3
    (SeitzExcAnisotropicForAt.of_cover (fun d p _ _ hT hQ => by
      obtain ⟨q, rfl⟩ := hT
      by_cases h : q.p = 2
      · exact Or.inl ⟨q, rfl, hQ, h⟩
      · exact Or.inr ⟨hQ, q, rfl, h⟩) (seitzExcAnisotropicForAt_triality_even hgold) hodd)

end Assembly

end CFSG.LieType.SeitzGeneration
