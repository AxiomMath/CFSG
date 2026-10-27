module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.Base
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenOneIGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenTwoIGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenThreeCaseGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenFiveMainGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixSixOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneKSField
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneCenterRankTwo
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneKSCenter
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneHolds
public import CFSG.LieType.OutStructureReductions
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixTwoComp
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineNineOneHolds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralHolds
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CKFactThreeFiveRankOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81COutRankOneBranch
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSmallKernelFiltrations
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowClassical
public import CFSG.Quasithin.EmptyFaithful.S14113bMain
public import CFSG.Quasithin.EmptyFaithful.T1515Der3
public import CFSG.Quasithin.EmptyFaithful.T1515Der4
public import CFSG.Quasithin.H13.A5S1520a
public import CFSG.Quasithin.H13.A6S1513
public import CFSG.Quasithin.H13.A6S4L1
public import CFSG.Quasithin.H13.U3L14E
public import CFSG.Quasithin.Vol2.Ch10SecAFactsOrth
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Facts
public import CFSG.Quasithin.Vol2.Ch6Sec1G22
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem11
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem12
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4R
public import CFSG.RankThree.PartOne.S11d.PSLRankTwoLow
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G}

namespace NineSettingGen

theorem nineTenConclusion_of_not_centralizer_le (hI : NineTenInputs)
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hU : NineNineOne M p) (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hNQ : normalizer (Q : Set G) ≤ M)
    (hQN : starImg p H Q ≤ compNormalizer (StarGroup p H))
    (hY : ¬ centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤ starImg p H M) :
    (¬ pLayerIn p H ≤ M → NineTenOne p M H) ∧
      (pLayerIn p H ≠ ⊥ → pLayerIn p H ≤ M → NineTenTwo p M H E) := by
  have hR : 2 ≤ CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) :=
    two_le_pRank_pCore h hU hQ hY
  refine ⟨?_, ?_⟩
  · intro hL
    have hL0 : pLayerIn p H ≠ ⊥ := fun hbot => hL (by rw [hbot]; exact bot_le)
    by_cases hp3 : p = 3
    · subst p
      exact nineTenOne_three (nineSixThree_of_kFacts CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central.kFactThreeFiveCentral_holds kFactThreeFiveRankOne_holds CFSG.RankThree.PartTwo.Sec4.Census.coverSLThree46) hI.sevenOne.twoOne
          (kFactCenterRankTwo_holds
              CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
              CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
              CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
        kFactCenterRankFive_holds h hH2 hp hR hY hL
    · exact absurd (nineTenTwo_five hI.sevenOne.twoOne (kFactCenterRankTwo_holds
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
        CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds) kFactCenterRankFive_holds
        sevenOneFourSplit sixSixOneRank_holds h hH2 hp hU hQ hY hL0 hp3).1 hL
  · intro hL0 hL
    by_cases hp3 : p = 3
    · subst p
      exact nineTenTwo_three hI.sevenOne.three hI hI.sevenOne.twoOne (kFactCenterRankTwo_holds
          CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
          CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
          CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
        kFactCenterRankFive_holds h hH2 hp hU hQ hNQ hQN hR hL0 hL
    · exact (nineTenTwo_five hI.sevenOne.twoOne (kFactCenterRankTwo_holds
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
        CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds) kFactCenterRankFive_holds
        sevenOneFourSplit sixSixOneRank_holds h hH2 hp hU hQ hY hL0 hp3).2

theorem nineTenConclusion_of_sylow (hI : NineTenInputs) (h : NineSettingGen G M p Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M) (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hNQ : normalizer (Q : Set G) ≤ M) :
    (¬ pLayerIn p H ≤ M → NineTenOne p M H) ∧
      (pLayerIn p H ≠ ⊥ → pLayerIn p H ≤ M → NineTenTwo p M H E) ∧
      (pLayerIn p H = ⊥ → NineTenThreeCorrected p M H) := by
  have hU : NineNineOne M p := CFSG.LocalAnalysis.AGL81TheoremCD.Section14.nineNineOneInput_holds G M Q H E p h hp
  have hkey : (¬ pLayerIn p H ≤ M → NineTenOne p M H) ∧
      (pLayerIn p H ≠ ⊥ → pLayerIn p H ≤ M → NineTenTwo p M H E) := by
    by_cases hQN : starImg p H Q ≤ compNormalizer (StarGroup p H)
    · by_cases hY : centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤
          starImg p H M
      · exact ⟨fun hL => nineTenOne_of_centralizer_le hI.sevenOne.three hI h hH2 hp
            hQ hNQ hQN hL hY,
          fun _ hL => absurd hY (not_centralizer_le_of_le hI.sevenOne.three hI h
            hH2 hp hQ hNQ hQN hL)⟩
      · exact nineTenConclusion_of_not_centralizer_le hI h hH2 hp hU hQ hNQ hQN hY
    · obtain ⟨-, hLM, h2⟩ := nineTenTwo_of_not_le_compNormalizer nineSixTwoComp_holds
        hI.sevenOne.three hI sevenOneFourField_holds hI.sevenOne.twoOne h hH2 hp hU hQ hQN
      exact ⟨fun hL => absurd hLM hL, fun _ _ => h2⟩
  exact ⟨hkey.1, hkey.2, fun hL => h.nineTenThreeCorrected CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.sixThreeOne_holds hH2 hp hU hL⟩

end NineSettingGen

theorem nineTenGen_of_inputs (hI : NineTenInputs) : NineTenGen := by
  intro G _ _ M Q H E p h hH2 hp
  have hU : NineNineOne M p := CFSG.LocalAnalysis.AGL81TheoremCD.Section14.nineNineOneInput_holds G M Q H E p h hp
  obtain ⟨P, -, hP, hH2P, hPH, -, hNP⟩ := h.exists_sylow_nineSetting hH2 hp hU
  exact NineSettingGen.nineTenConclusion_of_sylow hI hP hH2P hp hPH hNP

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
