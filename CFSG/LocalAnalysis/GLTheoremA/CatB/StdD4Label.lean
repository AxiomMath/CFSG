module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09LabelDict
public import CFSG.Blueprint.LieModelAPI
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.Models.Transport
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType TauCeti

theorem lieModel_omegaPlus_four_two {X : Type} [Group X]
    (hcat : catalogIs X CFSG.LocalAnalysis.GLTheoremA.S9.isD4two) :
    CFSG.Blueprint.LieModel X .POmegaPlus 4 2 1 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isD4two hcat
  have hm := CFSG.Models.lieModel_D 4 q hv e
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two (s := 1)
    (by norm_num) (hq.trans (by norm_num))
  rw [h1, h2] at hm
  exact hm.toBlueprint (by decide)

section Cert


theorem d4Label_of_marked {X : Type} [Group X] {lab : LargeEvenLabel}
    (hcat : catalogIs X CFSG.LocalAnalysis.GLTheoremA.S9.isD4two) (hM : MarkedModel lab X) :
    lab.tag = .D ∧ lab.rank = 4 := by
  have hG := lieModel_omegaPlus_four_two hcat
  obtain ⟨tg, r, nn⟩ := lab
  by_cases h2 : markChar ⟨tg, r, nn⟩ = 2
  · have hE : CFSG.Blueprint.LieModel X (markTag ⟨tg, r, nn⟩) (markRank ⟨tg, r, nn⟩) 2
        (markDeg ⟨tg, r, nn⟩) := by
      unfold MarkedModel at hM
      rwa [h2] at hM
    obtain ⟨e1, e2, -⟩ := CFSG.SeitzReduction.OmegaPilot.omegaEvenTypeDetAt 4 X .POmegaPlus 1
      (markTag ⟨tg, r, nn⟩) (markRank ⟨tg, r, nn⟩) (markDeg ⟨tg, r, nn⟩) (Or.inl rfl) hG hE.admissible hE
    cases tg
    all_goals simp only [markTag, markRank] at e1 e2 ⊢
    all_goals (try split_ifs at e1 e2 with h3)
    all_goals simp_all
  · cases tg <;> simp [markChar] at h2
    ·
      have hM' : CFSG.Blueprint.LieModel X .PSL 2 3 2 := hM
      have hodd : CFSG.Blueprint.OddLieType X :=
        ⟨.PSL, 2, 3, 2, Nat.prime_three, by decide, hM'.admissible, hM'⟩
      have key := CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hG (by decide) hodd
      simp at key
    ·
      have hM' : CFSG.Blueprint.LieModel X .PSU 3 3 1 := hM
      have hodd : CFSG.Blueprint.OddLieType X :=
        ⟨.PSU, 3, 3, 1, Nat.prime_three, by decide, hM'.admissible, hM'⟩
      have key := CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hG (by decide) hodd
      simp at key

end Cert

end CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4
