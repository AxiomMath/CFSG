module

public import CFSG.LocalAnalysis.ComponentClassification.CTUFrontierFlat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82KStatements
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.Milestones.CL_LIT_classical_involution_theorem

public section

namespace CFSG.ComponentClassification.GSRedNoB2L

section M78

open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr in
theorem m78_of_yardstonesGS
    (hGH : type_of% @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (hCI : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (h01 : Sol76.Sig.Lemma39TwoDiscK2At Sol76.Sig.solRestrictedHub)
    (h02 : Sol76.Sig.QuasisimpleSylowFourJoinedSCN)
    (h03 : Sol76.Sig.SolomonQTwoDisconnectedSylowInvFor) (h04 : GSThmB.Solomon2AnInput)
    (h05 : SolAltLit.AltStdCyclicOddTwoFalse) (h06 : SolMax.SwapP2.SwapMemberResidueNineExact)
    (h07 : SolMax.SwapP2.SwapMemberResidueNineExoticT2)
    (h08 : SolMax.SwapP2.SwapMemberResidueNineExoticT3)
    (h09 : SolMax.SignalizerNineSixDihedralLocalInput)
    (h12 : GSLit.GriessSolomonInput) (h14 : GSThmB.GS82CentXA10TransferStatementK)
    (h15 : GSThmB.GS82Step2FuseStatementK) :
    ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X],
      (∃ a b : X, a * b ≠ b * a) → Assembly.KProper Blueprint.Catalog X →
      (∃ z : X, orderOf z = 2 ∧ oddCore (Subgroup.centralizer ({z} : Set X)) ≠ ⊥) →
      ¬ OutcomeLocal.UOutcome X →
      (∃ (a b : X) (J : Subgroup X), GSUnbalancingTriple a b J) →
      ∃ (x y : X) (L : Subgroup X), GSMaximalUnbalancingTriple x y L ∧
        GSMaximalComponent L ∧
        ((Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
          ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
            Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) ∨
         (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
           Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2)) := by
  obtain ⟨hTB, hSA, hGS, hB, hH⟩ := KProperRelativeB.gsInputs_of_flatLeavesGS hGH hCI
    (Sol76.Sig.lemma315bInputFor_simple_of_hbK2Leaves h01 h02 h03) h04 h05 h06 h07 h08 h09
    h12 h14 h15
  exact GSLit.cl_lit_gilman_solomon_native_of_inputs hTB hSA hGS hB hH
    GSLit.globallyFirstRankTwoInput_holds

end M78

section CTU

theorem ctu_kproper_simple_unbalanced_recognition_models_of_yardstonesGS
    (hGH : type_of% @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (hCI : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (y01 : CFSG.OddStandard.Solomon75.Solomon75LocalStructure)
    (y02 : SolAltLit.AltStdCyclicOddTwoFalse)
    (y03 : SolMax.SwapP2.SwapMemberResidueNineExact)
    (y04 : SolMax.SwapP2.SwapMemberResidueNineExoticT2)
    (y05 : SolMax.SwapP2.SwapMemberResidueNineExoticT3)
    (y06 : SolMax.SignalizerNineSixDihedralLocalInput)
    (y08 : GSLit.GriessSolomonInput)
    (y09 : FooteLit.FooteMaximalUnbalancedInput)
    (y11 : GSThmB.GS82CentXA10TransferStatementK)
    (y12 : GSThmB.GS82Step2FuseStatementK)
    (y13 : Sol76.Sig.Lemma39TwoDiscK2At Sol76.Sig.solRestrictedHub)
    (y14 : Sol76.Sig.QuasisimpleSylowFourJoinedSCN)
    (y15 : Sol76.Sig.SolomonQTwoDisconnectedSylowInvFor)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (z : G) (hz : orderOf z = 2)
    (hunbal : CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) :
    (CFSG.Blueprint.OddLieType G ∨
      ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∧
      CFSG.Blueprint.Catalog G := by
  have hGHInput : UFrontier.GH74ModelsInput := hGH
  have hCIInput : GSLit.ClassicalInvolutionInput := hCI
  exact CTUSimple.ctu_kproper_simple_unbalanced_recognition_models_of_flatK2LeavesGS
    hGHInput hCIInput y13 y14 y15
    { h2An := CFSG.OddStandard.Solomon75.solomon2AnInput_of_localStructure
        CFSG.OddStandard.Solomon75.solomon44McL_of_certificate
        (CFSG.OddStandard.Solomon75.solomon44Ly_of_gh74_of_certificate hGHInput)
        CFSG.OddStandard.Solomon75.solomon44NineTen_of_certificate y01
      hSCAT2 := y02
      hSwX := y03
      hSw9T2 := y04
      hSw9T3 := y05
      hFC6' := y06
      hGS := y08
      hFMU := y09
      hZA10T := y11
      h2z := y12 }
    G hnonab hK z hz hunbal

theorem ctu_kproper_simple_unbalanced_recognition_of_yardstonesGS
    (hGH : type_of% @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (hCI : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (y01 : CFSG.OddStandard.Solomon75.Solomon75LocalStructure)
    (y02 : SolAltLit.AltStdCyclicOddTwoFalse)
    (y03 : SolMax.SwapP2.SwapMemberResidueNineExact)
    (y04 : SolMax.SwapP2.SwapMemberResidueNineExoticT2)
    (y05 : SolMax.SwapP2.SwapMemberResidueNineExoticT3)
    (y06 : SolMax.SignalizerNineSixDihedralLocalInput)
    (y08 : GSLit.GriessSolomonInput)
    (y09 : FooteLit.FooteMaximalUnbalancedInput)
    (y11 : GSThmB.GS82CentXA10TransferStatementK)
    (y12 : GSThmB.GS82Step2FuseStatementK)
    (y13 : Sol76.Sig.Lemma39TwoDiscK2At Sol76.Sig.solRestrictedHub)
    (y14 : Sol76.Sig.QuasisimpleSylowFourJoinedSCN)
    (y15 : Sol76.Sig.SolomonQTwoDisconnectedSylowInvFor)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (z : G) (hz : orderOf z = 2)
    (hunbal : CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) :
    CFSG.Blueprint.OddLieType G ∨
      ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n)) := by
  exact (ctu_kproper_simple_unbalanced_recognition_models_of_yardstonesGS
    hGH hCI y01 y02 y03 y04 y05 y06 y08 y09 y11 y12 y13 y14 y15 G hnonab hK z hz hunbal).1

end CTU

section CTB

theorem ctb_kproper_component_local_b_of_yardstonesGS
    (hGH : type_of% @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (hCI : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (ys01 : Sol76.Sig.Lemma39TwoDiscK2At Sol76.Sig.solRestrictedHub)
    (ys02 : Sol76.Sig.QuasisimpleSylowFourJoinedSCN)
    (ys03 : Sol76.Sig.SolomonQTwoDisconnectedSylowInvFor)
    (ys04 : GSThmB.Solomon2AnInput)
    (ys05 : SolAltLit.AltStdCyclicOddTwoFalse)
    (ys06 : SolMax.SwapP2.SwapMemberResidueNineExact)
    (ys07 : SolMax.SwapP2.SwapMemberResidueNineExoticT2)
    (ys08 : SolMax.SwapP2.SwapMemberResidueNineExoticT3)
    (ys09 : SolMax.SignalizerNineSixDihedralLocalInput)
    (ys12 : GSLit.GriessSolomonInput)
    (ys13 : FooteLit.FooteMaximalUnbalancedInput)
    (ys14 : GSThmB.GS82CentXA10TransferStatementK)
    (ys15 : GSThmB.GS82Step2FuseStatementK) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → CFSG.Assembly.IsComponentType G →
        CFSG.Assembly.oddCore G = ⊥ ∧ CFSG.Assembly.ComponentType.LocalBProperty G := by
  intro G _ _ _ _ hK hcomp
  exact KProperRelativeB.kProper_component_local_B_of_flatLeavesGS
    (by intro X _ _ _; exact hGH X) (by intro X _ _ _; exact hCI X)
    (Sol76.Sig.lemma315bInputFor_simple_of_hbK2Leaves ys01 ys02 ys03)
    ys04 ys05 ys06 ys07 ys08 ys09 ys12 ys13 ys14 ys15 G hK hcomp

end CTB

end CFSG.ComponentClassification.GSRedNoB2L
