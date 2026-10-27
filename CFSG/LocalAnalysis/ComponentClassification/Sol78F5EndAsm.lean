module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGMain
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieExc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieOMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieSp
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L513D
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511AA
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Setting
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankBound
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Data
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL24V
public import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSmallCent
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Uniq
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGFinal
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches
import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalance
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteLit
import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsFull
import CFSG.Alternating.Multipliers.Main
import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.GH74.Generic.S45.LEvSporGen
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LieType.Ree.SmallReeInvolutionComponents
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7TwistMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTrialityInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE8
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormF4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormRee
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSporadic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6Graph
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.RankThree.PartTwo.Census.Spin.Main
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import Certificates.Certificate8171
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5

variable {G : Type} [Group G] [Finite G]

theorem Hyp.of_inputs
    (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups) (hB4 : GoldschmidtCorB4)
    (hMW : MacWilliamsStatement) (hDiag : Foote5DiagonalNotInQ)
    {L₀ L Q S T : Subgroup G} {z₀ t : G} (h : Sec5 G L₀ L Q S T z₀ t) :
    ∃ (L' : Subgroup G) (s : G) (Lin : Subgroup (MulAut (L₀ ⧸ Open.fusionZStar L₀)))
      (ε : L' ⧸ pPrimeCore 2 L' ≃* L₀ ⧸ Open.fusionZStar L₀),
      Hyp L₀ L' Q S T (s⁻¹ * t * s) t s ε Lin := by
  have hAut := foote5AutStructure_holds
  have hFC := Sol78.foote5FieldCentralizer
  have hST := h.not_isSylowOf_top hGH hKG hB4 hAut
  have hSlt : S < T := lt_of_le_of_ne h.ST fun h1 => hST (by rw [h1]; exact h.sylT)
  obtain ⟨s, hsT, hsS, -, -, -, hQQs, -⟩ := h.exists_s_of_lt hSlt
  obtain ⟨h', -⟩ := h.repoint_conj_t hGH hKG hB4 hAut hMW hFC hsT hsS
  obtain ⟨Lin, hD⟩ := h'.exists_autData hAut
  obtain ⟨ε⟩ := h'.quotient_simple.2
  have hT2 := h'.card_T_eq_two_mul hGH hKG hB4 hAut hMW hFC
  have hna := h'.nonabelian_R_of_not_sylow hGH hKG hAut hMW
    (h'.not_isSylowOf_top hGH hKG hB4 hAut)
  have hCt : ∀ y ∈ T, y * t = t * y → y ∈ S := fun y hy hyt =>
    h'.mem_S_of_commute_t_of_inputs hGH hKG hB4 hAut hMW hFC hy hyt
  exact ⟨_, s, Lin, ε,
    { sec5 := h'
      autData := hD
      sT := hsT
      sS := hsS
      hz := rfl
      cardT := hT2
      centT := hCt
      nonab := hna
      QQs := hQQs
      e8 := h'.exists_normal_e8_zt ε hMW hGH hKG hD hna hCt hT2 hsT hsS
      l511 := h'.conjugate_R_le_Q hGH hKG hB4 hAut hMW hFC hDiag hsT hsS
      l512 := fun g hg => h'.lemma512 hGH hKG hB4 hAut hMW hDiag foote5Lemma24iiV_holds
        hsT hsS rfl hg
      l513 := h'.lemma513 hGH hKG hB4 hAut hMW hDiag ε hD hsT hsS rfl }⟩

theorem false_of_rank_two_counterexample
    (hLB : FooteLBalanceInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hSolv : FooteL2InvolutionSolvable) (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hB4 : GoldschmidtCorB4) (hMW : MacWilliamsStatement)
    (h3 : Asc76.Asc76Theorem3Large)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hKGE : Foote5.EndKnownGroupsInput)
    {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L) (hsimple : IsSimpleGroup G)
    (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2)
    (hex : ∃ A ∈ footeFamilyOf L, 2 ≤ CFSG.pRank 2 ↥(coreActionKernel A))
    (hrankC : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2) :
    False := by
  have hsec := Foote5.footeSec4_of_rank_le_two hLB hCI hGA hGC hSA hOut hAb h9 hRk hSolv hce
    hsimple hrank2 hrankC
  obtain ⟨L', Q, S, T, z, t', h5⟩ := exists_sec5 hsec hrankC hex
  have hDiag := foote5DiagonalNotInQ_of_inputs hMW hGH hKG
  obtain ⟨L'', s, Lin, ε, H⟩ := Hyp.of_inputs hGH hKG hB4 hMW hDiag h5
  exact Foote5.false_of_hyp_endKnownGroupsInput H h3 hK hcalc hKGE

theorem footeRankTwoExclusion_of_inputs
    (hLB : FooteLBalanceInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hSolv : FooteL2InvolutionSolvable) (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hB4 : GoldschmidtCorB4) (hMW : MacWilliamsStatement)
    (h3 : Asc76.Asc76Theorem3Large)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hKGE : Foote5.EndKnownGroupsInput) : FooteRankTwoExclusion := by
  intro G _ _ t L _hmin hce hsimple hrank2 hex hrankC
  exact false_of_rank_two_counterexample hLB hCI hGA hGC hSA hOut hAb h9 hRk hSolv hGH hKG
    hB4 hMW h3 hK hcalc hKGE hce hsimple hrank2 hex hrankC

theorem footeRankTwoExclusion_of_open_inputs
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGH : UFrontier.GH74ModelsInput) (hB4 : GoldschmidtCorB4) :
    FooteRankTwoExclusion :=
  footeRankTwoExclusion_of_inputs footeLBalanceInput_holds hCI hGA
    CFSG.RankThree.PartTwo.Sec4.Census.griessMultipliersCentralCovers
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput AutL2Facts.cfFooteL2OutAbelian
    AutL2Facts.cfFooteL2AbelianCore AutL2Facts.cfFooteL2NineOddInner AutL2Facts.cfFooteL2RankThree
    AutL2Facts.cfFooteL2InvolutionSolvable
    (fun X _ _ hs hna h3 hgen => @hGH X _ _ hs hna h3 hgen) foote5KnownGroups_holds hB4
    (fun _ _ _ hS hE => CFSG.LargeEvenClassification.Helpers.macwilliams_four_generators hS hE)
    RankTwoFoundation.asc76Theorem3Large AschbacherKnownGroup.knownGroupFacts_holds
    footeSmallCentralizers_holds
    (endKnownGroupsInput_of_oddLie_sporadic
        (Sol78.F514.endOddLieInput_of_for CatLeafProof.endOddLieInputFor_oddExceptional
            CatLeafProof.EndOddLin.endOddLieInputFor_PSL_PSU
            CatLeafProof.EndOddSp.endOddLieInputFor_PSp
            CatLeafProof.EndOddO.endOddLieInputFor_orthogonal) endKnownGroupsInputOn_sporadic)

end CFSG.ComponentClassification.Sol78.F514
