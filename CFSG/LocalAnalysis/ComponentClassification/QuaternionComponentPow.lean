module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired14
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4GB

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly

set_option linter.unusedSectionVars false

section Channel

@[expose] def CITPowBelow3 : Prop :=
  ∀ m : ℕ, Q3.CIT3Below m → Asc77.CITBelowAll 3 m

theorem citPowBelow3_of_minimal {n : ℕ} (hAll : Asc77.CITBelowAll 3 n)
    (hbig : ¬ Q3.CIT3Below (n + 1)) : CITPowBelow3 :=
  fun _ hB => Q3.JI.citBelowAll_of_minimal hAll hbig hB

end Channel

section Discharge

theorem cit3StepJ_of_gh74_memberFreeP (hGH : GH74SectionalModels)
    (hMFS : CITPowBelow3 → Q3.Q3T.MemberFreeSocleOuter3) (n : ℕ) : Q3.JI.CIT3StepJ n := by
  intro hn hAll
  by_cases hbig : Q3.CIT3Below (n + 1)
  · exact fun Y _ _ hY Λ hΛ => hbig Y (hY ▸ Nat.lt_succ_self n) Λ hΛ
  · exact cit3StepJ_of_gh74_memberFree hGH (hMFS (citPowBelow3_of_minimal hAll hbig)) n hn hAll

theorem citPowBelow3_of_gh74_memberFreeP (hGH : GH74SectionalModels)
    (hMFS : CITPowBelow3 → Q3.Q3T.MemberFreeSocleOuter3) : CITPowBelow3 := fun m _ =>
  (Q3.JI.joint_induction (cit3StepJ_of_gh74_memberFreeP hGH hMFS) (coreStep3Pow_of_gh74 hGH)
    (fun _ => ModelFacts.classicalIsFundamental_of_exc ModelFacts.classicalMembersFundamentalExc)
    (ModelFacts.centralLift 3) m).2

end Discharge

section Leaf

theorem tightE4VtxSR_of_pow (gp : CITPowBelow3) (n : ℕ) : Q3.TL4.TightE4VtxSR 3 n :=
  fun Y _ _ R S t hL => Q3.TL4.tightE4VtxSR_three (gp n hL.below 2 (by norm_num)) Y R S t hL

end Leaf

end CFSG.ComponentClassification.QuaternionComponent
