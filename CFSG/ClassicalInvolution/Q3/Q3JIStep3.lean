module

public import CFSG.ClassicalInvolution.Q3.Q3RCoreStepPieces
public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.JI

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Step3

@[expose] def CoreStep3LargeJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      Asc77.CITBelowAll 3 (Nat.card G) → 3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G →
      LieSystem3 G (Set.range fun g : G => conjSub g K)

theorem citBelowAll_mono {p : ℕ} [Fact p.Prime] {m n : ℕ} (h : m ≤ n)
    (hn : Asc77.CITBelowAll p n) : Asc77.CITBelowAll p m :=
  fun e he => CITBelowU.mono p e h (hn e he)

theorem citBelowAll_of_minimal {n m : ℕ} (hAll : Asc77.CITBelowAll 3 n)
    (hbig : ¬ CIT3Below (n + 1)) (hB : CIT3Below m) : Asc77.CITBelowAll 3 m := by
  refine citBelowAll_mono ?_ hAll
  by_contra h
  exact hbig (CIT3Below.mono (by omega) hB)

theorem coreStep3Large_of_minimal (hJ : CoreStep3LargeJ) {n : ℕ} (hAll : Asc77.CITBelowAll 3 n)
    (hbig : ¬ CIT3Below (n + 1)) : CoreStep3Large := by
  intro G _ _ _ hnab K z hK hBelow h3 h4
  by_cases hle : Nat.card G ≤ n
  · exact hJ G hnab K z hK hBelow (citBelowAll_mono hle hAll) h3 h4
  · exact absurd (CIT3Below.mono (by omega) hBelow) hbig

@[expose] def CIT3StepJ (n : ℕ) : Prop :=
  CIT3Below n → Asc77.CITBelowAll 3 n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ Λ : Set (Subgroup Y), InClass3 Λ → LieSystemMod3 Λ

theorem cit3StepJ_of_parts (hS : SolvableConnected3) (hQ : QuasisimpleConnected3)
    (hfund : ClassicalIsFundamental3) (hlift : CentralLift 3) (hM11 : M11Branch3)
    (hcore : CoreStep3Large → CoreStep3) (hJ : CoreStep3LargeJ) (n : ℕ) : CIT3StepJ n := by
  intro hn hAll
  have hnext : CIT3Below (n + 1) := by
    by_contra hbig
    have hstep : CIT3Step n := cit3Step_of_connectedBranch
      (connectedBranch3_of_parts hS hQ (hcore (coreStep3Large_of_minimal hJ hAll hbig)) hfund hlift
        hM11) n
    exact hbig fun Y _ _ hY Λ hΛ => (Nat.lt_succ_iff_lt_or_eq.mp hY).elim
      (fun hlt => hn Y hlt Λ hΛ) fun heq => hstep hn Y heq Λ hΛ
  intro Y _ _ hY Λ hΛ
  exact hnext Y (hY ▸ Nat.lt_succ_self n) Λ hΛ

end Step3

end CFSG.ClassicalInvolution.Q3.JI
