module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RLeaf
public import CFSG.ClassicalInvolution.Uniform.UInduction
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Generic

section Step


@[expose] def A7StepJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), Hat2A7.IsClassical2A7 ⊤ K z →
      Hat2A7.CITBelow2A7 (Nat.card G) → CITBelowAllT 3 (Nat.card G) →
      CITBelowAllT 5 (Nat.card G) → False

theorem coreStep2A7_of_stepJ (hJ : A7StepJ)
    (hSL : ∀ n, CITBelowAllT 3 n ∧ CITBelowAllT 5 n) : Hat2A7.CoreStep2A7 :=
  fun G _ _ _ hnab K z hK hB => hJ G hnab K z hK hB (hSL _).1 (hSL _).2

theorem a7ThmI_of_stepJ (hJ : A7StepJ)
    (hSL : ∀ n, CITBelowAllT 3 n ∧ CITBelowAllT 5 n) : A7ThmI :=
  a7ThmI_of_coreStep2A7 (coreStep2A7_of_stepJ hJ hSL)

theorem citBelowT_three_of_inductive (h : Q3.CIT3Inductive) (n : ℕ) :
    CITBelowT (.sl2 3 1) n :=
  (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr
    (fun Y _ _ _ Λ hΛ => h Y Λ hΛ)

theorem citBelowAllT_three_of_inductive (h1 : Q3.CIT3Inductive) (hU : ∀ f, CITInductiveU 3 f)
    (n : ℕ) : CITBelowAllT 3 n := by
  intro e he
  rcases Nat.lt_or_ge e 2 with h | h
  · interval_cases e
    · norm_num at he
    · exact citBelowT_three_of_inductive h1 n
  · have hq : 5 ≤ 3 ^ e := by
      calc 5 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) h
    exact (citBelowT_iff_citBelowU (p := 3) (f := e) (by norm_num) hq n).mpr
      (fun Y _ _ _ Λ hΛ => hU e (by norm_num) hq Y Λ hΛ)

theorem citBelowAllT_five_of_inductiveU [Fact (Nat.Prime 5)] (hU : ∀ f, CITInductiveU 5 f)
    (n : ℕ) : CITBelowAllT 5 n := by
  intro e he
  have hq : 5 ≤ 5 ^ e := by
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · norm_num at he
    · exact Nat.le_self_pow hpos.ne' 5
  exact (citBelowT_iff_citBelowU (p := 5) (f := e) (by norm_num) hq n).mpr
    (fun Y _ _ _ Λ hΛ => hU e (by norm_num) hq Y Λ hΛ)

theorem a7ThmI_of_stepJ_of_inductive [Fact (Nat.Prime 5)] (hJ : A7StepJ) (h3 : Q3.CIT3Inductive)
    (hU3 : ∀ f, CITInductiveU 3 f) (hU5 : ∀ f, CITInductiveU 5 f) : A7ThmI :=
  a7ThmI_of_stepJ hJ fun n =>
    ⟨citBelowAllT_three_of_inductive h3 hU3 n, citBelowAllT_five_of_inductiveU hU5 n⟩

end Step

end CFSG.ClassicalInvolution.Hat2A7R
