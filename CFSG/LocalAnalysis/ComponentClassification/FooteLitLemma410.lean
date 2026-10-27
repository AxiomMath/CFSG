module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Seven
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankBound
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteRooted
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteLit
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Nine

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB

theorem footeLemma410Statement_of_inputs
    (h47 : FooteThm47Statement) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) : FooteLemma410Statement := by
  intro G _ _ L h htype M hM g E hE hE2 hE8
  by_contra hcon
  have hinv : ¬ ∃ x ∈ coreActionKernel M ⊓ coreActionKernel (conjugate M g), orderOf x = 2 :=
    fun h1 => hcon (Or.inl h1)
  have hMN : ¬ M ≤ normalizer (conjugate M g : Set G) := fun h1 => hcon (Or.inr h1)
  obtain ⟨Q, t, hc⟩ := exists_foote410Config h h47 GSThmB.suzukiTausskyInput
    GSThmB.aschbacherTheorem5Input_holds AutL2Facts.footeFourgroupE8
    AschbacherKnownGroup.knownGroupFacts_holds footeSmallCentralizers_holds
    AutL2Facts.footeFourgroupInner htype hM hE hE2 hE8 hinv hMN
  have htK := hc.not_mem_footeK h h47 GSThmB.suzukiTausskyInput hAsc h2An hM
  rcases htype with hseven | hnine
  · exact hc.false_of_seven h h47 GSThmB.suzukiTausskyInput hAsc h2An hM htK hseven
  · exact hc.false_of_nine h h47 GSThmB.suzukiTausskyInput hAsc h2An hM htK hnine

theorem footeRankBound_of_known_inputs_410
    (hLB : FooteLBalanceInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hSA : SolAltLit.SchurAlternatingMultiplierInput)
    (hSol : Sol76T13.SolomonThm13Simple) (hM3 : FooteSolomonFamilyInput) (h47 : FooteThm47Statement)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) : FooteRankBound :=
  footeRankBound_of_open_inputs hLB hCI hGA hSA AutL2Facts.cfFooteL2OutAbelian
      AutL2Facts.cfFooteL2AbelianCore AutL2Facts.cfFooteL2NineOddInner AutL2Facts.cfFooteL2RankThree
      AutL2Facts.cfFooteL2InvolutionSolvable hSol hM3 h47 hAsc h2An AutL2Facts.footeFourgroupE8
      footeSmallCentralizers_holds AutL2Facts.footeFourgroupInner AutL2Facts.footeL2RootedOuter
      AutL2Facts.footeAutRankThree AutL2Facts.footeL2FourgroupGeneration
      (footeLemma410Statement_of_inputs h47 hAsc h2An)

end CFSG.ComponentClassification.FooteLit
