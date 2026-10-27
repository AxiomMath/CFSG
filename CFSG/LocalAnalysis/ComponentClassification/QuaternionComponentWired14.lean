module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired14
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentBridge
public import CFSG.Adapters.TauCetiExceptional.ReeCatalog

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly

set_option linter.unusedSectionVars false

theorem cit3StepJ_of_gh74_memberFree (hGH : GH74SectionalModels)
    (hMFS : Q3.Q3T.MemberFreeSocleOuter3) (n : ℕ) : Q3.JI.CIT3StepJ n :=
  have hq3 : W14.Q3Residuals₁₄ := ⟨hMFS⟩
  Q3.JI.cit3StepJ_of_parts Q3.SP3.solvableConnected3 hq3.quasisimple
    Q3.classicalIsFundamental3_proved (ModelFacts.centralLift 3) Q3.m11Branch3
    (fun hl => Q3.coreStep3_of_gh74_proved hGH Q3.sectionalFourNonLie3_proved hl) hq3.largeJ n

theorem coreStep3Pow_of_gh74 (hGH : GH74SectionalModels) :
    ∀ (n e : ℕ), 5 ≤ 3 ^ e → Q3.CIT3Below (n + 1) → Asc77.CITBelowAll 3 n →
      ¬ Generic.CITBelowU 3 e (n + 1) → Generic.CoreStep 3 e :=
  fun n e _ hB hAll hbig => (W14.coreOpenWired₁₄_proved 3 e).toCoreStepAt hGH
    ComponentClassification.RankTwoFoundation.asc75Theorem4 (W14.ihInterface8_proved 3) n hB hAll
    hbig

theorem jointBelow_of_gh74_memberFree (hGH : GH74SectionalModels)
    (hMFS : Q3.Q3T.MemberFreeSocleOuter3) (n : ℕ) :
    Q3.CIT3Below n ∧ Asc77.CITBelowAll 3 n :=
  Q3.JI.joint_induction (cit3StepJ_of_gh74_memberFree hGH hMFS) (coreStep3Pow_of_gh74 hGH)
    (fun _ => ModelFacts.classicalIsFundamental_of_exc ModelFacts.classicalMembersFundamentalExc)
    (ModelFacts.centralLift 3) n

theorem joint_of_gh74_memberFree (hGH : GH74SectionalModels)
    (hMFS : Q3.Q3T.MemberFreeSocleOuter3) :
    Q3.CIT3Inductive ∧ ∀ e : ℕ, Generic.CITInductiveU 3 e :=
  Q3.JI.cit3_and_citInductiveU_of_joint (cit3StepJ_of_gh74_memberFree hGH hMFS)
    (coreStep3Pow_of_gh74 hGH)
    (fun _ => ModelFacts.classicalIsFundamental_of_exc ModelFacts.classicalMembersFundamentalExc)
    (ModelFacts.centralLift 3)

theorem coreStep3Large_of_gh74_memberFree (hGH : GH74SectionalModels)
    (hMFS : Q3.Q3T.MemberFreeSocleOuter3) : Q3.CoreStep3Large :=
  have hq3 : W14.Q3Residuals₁₄ := ⟨hMFS⟩
  fun _ _ _ _ hnab K z hz hB h3 h4 =>
    hq3.largeJ _ hnab K z hz hB (jointBelow_of_gh74_memberFree hGH hMFS _).2 h3 h4

theorem a7ThmI_of_gh74_memberFree (hGH : GH74SectionalModels)
    (hMFS : Q3.Q3T.MemberFreeSocleOuter3) : Hat2A7R.A7ThmI :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  Hat2A7R.a7ThmI_of_stepJ_of_inductive
    (Hat2A7R.a7StepJ_of_gh74_tc hGH (Hat2A7S.a7TC_proved Hat2A7S.a7ThmE_proved
      (Hat2A7.goldschmidtStronglyClosedExponent_of_milestone
        @CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian)))
    (joint_of_gh74_memberFree hGH hMFS).1 (joint_of_gh74_memberFree hGH hMFS).2
    (fun f => W14.citInductiveU_of_wired₁₄ (p := 5) hGH
      ComponentClassification.RankTwoFoundation.asc75Theorem4
      (fun e _ _ => W14.coreOpenWired₁₄_proved 5 e) (joint_of_gh74_memberFree hGH hMFS).1 f)

theorem partOne_of_gh74_memberFree (hGH : GH74SectionalModels)
    (hMFS : Q3.Q3T.MemberFreeSocleOuter3) : PartOne :=
  have hq3 : W14.Q3Residuals₁₄ := ⟨hMFS⟩
  partOne_of_l2PrimeBalance l2PrimeBalance
    (W14.citSimplePerfect_of_wired₁₄ hGH ComponentClassification.RankTwoFoundation.asc75Theorem4
      (fun p f _ _ _ => W14.coreOpenWired₁₄_proved p f) (joint_of_gh74_memberFree hGH hMFS).1
      (a7ThmI_of_gh74_memberFree hGH hMFS))
    (q3Inputs₅_of_residuals_proved hGH hq3.quasisimple Q3.sectionalFourNonLie3_proved
      (coreStep3Large_of_gh74_memberFree hGH hMFS)).partOneSolvable

theorem milestone_of_gh74_memberFree (hGH : GH74SectionalModels)
    (hMFS : Q3.Q3T.MemberFreeSocleOuter3)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hJ : Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)))
    (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Assembly.ComponentType.OddLieType G ∨ Nonempty (G ≃* Assembly.ComponentType.M11) :=
  milestone_of_partOne_of_oddLieType (partOne_of_gh74_memberFree hGH hMFS) G hnonab
    (fun hL => TauCetiBridge.componentType_oddLieType_of_blueprint_of_odd G hL) z hz J hJ hzJ S hS

end CFSG.ComponentClassification.QuaternionComponent
