module

public import CFSG.ClassicalInvolution.Q3.Q3JIStep3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.JI

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Joint


theorem joint_induction (hQ3 : ∀ n, CIT3StepJ n)
    (hQ5 : ∀ (n f : ℕ), 5 ≤ 3 ^ f → CIT3Below (n + 1) → Asc77.CITBelowAll 3 n →
      ¬ CITBelowU 3 f (n + 1) → CoreStep 3 f)
    (hfund : ∀ f : ℕ, ClassicalIsFundamental 3 f) (hlift : CentralLift 3) (n : ℕ) :
    CIT3Below n ∧ Asc77.CITBelowAll 3 n := by
  induction n with
  | zero =>
    exact ⟨fun Y _ _ hY => absurd hY (Nat.not_lt_zero _),
      fun e _ Y _ _ hY => absurd hY (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨hB, hAll⟩ := ih
    have hB' : CIT3Below (n + 1) := by
      intro Y _ _ hY Λ hΛ
      rcases Nat.lt_succ_iff_lt_or_eq.mp hY with hlt | heq
      · exact hB Y hlt Λ hΛ
      · exact hQ3 n hB hAll Y heq Λ hΛ
    refine ⟨hB', ?_⟩
    intro f hq
    by_contra hbig
    have hstep := citStepU_of_coreStep (hQ5 n f hq hB' hAll hbig) (hfund f) hlift n
      (by norm_num) hq (hAll f hq)
    exact hbig fun Y _ _ hY Λ hΛ => (Nat.lt_succ_iff_lt_or_eq.mp hY).elim
      (fun hlt => hAll f hq Y hlt Λ hΛ) fun heq => hstep Y heq Λ hΛ

theorem cit3_and_citInductiveU_of_joint (hQ3 : ∀ n, CIT3StepJ n)
    (hQ5 : ∀ (n f : ℕ), 5 ≤ 3 ^ f → CIT3Below (n + 1) → Asc77.CITBelowAll 3 n →
      ¬ CITBelowU 3 f (n + 1) → CoreStep 3 f)
    (hfund : ∀ f : ℕ, ClassicalIsFundamental 3 f) (hlift : CentralLift 3) :
    CIT3Inductive ∧ ∀ e : ℕ, CITInductiveU 3 e := by
  have hj := joint_induction hQ3 hQ5 hfund hlift
  exact ⟨fun Y _ _ Λ hΛ => (hj (Nat.card Y + 1)).1 Y (Nat.lt_succ_self _) Λ hΛ,
    fun e _ hq Y _ _ Λ hΛ => (hj (Nat.card Y + 1)).2 e hq Y (Nat.lt_succ_self _) Λ hΛ⟩

end Joint

end CFSG.ClassicalInvolution.Q3.JI
