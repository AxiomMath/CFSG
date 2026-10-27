module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.InputSecond
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairExists
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairOctad
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairCompat
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.OctadMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.NineMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ThirteenMain

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_firstHalf
    {L : Subgroup G} {z : G} (hs : LocalSetting G L z) (hcase : CaseTwo L z) :
    ∃ A B C D : Subgroup G, FirstHalfData L z A B C D := by
  obtain ⟨A, B, hP⟩ := exists_pairType hs.sporadic
  have hA := hP.sextet
  have hB := hP.octad
  have hSF := sextetFacts_of_type hA
  have hSQ := sextetFactsQW_of_type hA
  have hOB := octadBasics_of_type hB
  have hCF := compatFacts_of_pair hP
  have hLift := liftDataB_of_type hB
  have hSp := splitDataB_of_type hB
  have hcaseA : ¬ egM A z ≤ centralizer ({z} : Set G) :=
    hcase A hA.1 hSF.elem.1 hSF.elem.2 hSF.card_A
  have hT := translationData_of_sextetFacts hs hA.1 (sextetFacts_of_type hA) hcaseA
  obtain ⟨C, hC⟩ := exists_cData_of_W hs hA hSF hSQ hT
  have hcaseB := caseTwoB hs hSF hOB hCF hC
  obtain ⟨D, hD⟩ := exists_nData hs hB hOB hLift hSp hcaseB
  exact ⟨A, B, C, D, ⟨hP, hSF, hOB, hCF, hT, hC, cData_elem hs hCF hT hC hD, hD⟩⟩

end CFSG.EvenSporadicStandard.M24Std
