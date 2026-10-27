module

public import CFSG.ClassicalInvolution.Q3.Q3TIYFinal
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.RouteD.TWY
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinRow)

@[expose] def TwinRowMid3 (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)

theorem exists_of_card_mul_ne {α : Type*} {p : α → Prop} {O m : ℕ}
    (h : Nat.card {a // p a} * O = 2 * m) (hm : m ≠ 0) : ∃ a, p a := by
  by_contra hne
  push Not at hne
  have : IsEmpty {a // p a} := ⟨fun ⟨a, ha⟩ => hne a ha⟩
  rw [Nat.card_of_isEmpty, zero_mul] at h
  omega

theorem twinCentralizingNe3_odd {n : ℕ} (hn : 3 ≤ n) : TwinCentralizingNe3 .POmegaOdd n := by
  intro R R' x x' ã ã' hd hãR hã'R hsq hsq'
  obtain ⟨S, hS, hSle⟩ := exists_of_card_mul_ne (p := fun S : Subgroup
    (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K => S ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D ∧ S ≤ Subgroup.centralizer
      ({ã * ã'} : Set (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K))
    (card_fund_centralizing3_odd hn hd hãR hã'R hsq hsq')
    (framesOdd_ne_zero (q := 3) (by norm_num) _)
  exact ⟨S, hS, hSle⟩

theorem twinCentralizingNe3_minus {n : ℕ} (hn : 4 ≤ n) : TwinCentralizingNe3 .POmegaMinus n := by
  intro R R' x x' ã ã' hd hãR hã'R hsq hsq'
  obtain ⟨S, hS, hSle⟩ := exists_of_card_mul_ne (p := fun S : Subgroup
    (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K => S ∈ fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D ∧ S ≤ Subgroup.centralizer
      ({ã * ã'} : Set (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K))
    (card_fund_centralizing3_minus hn hd hãR hã'R hsq hsq')
    (framesPlus_ne_zero (q := 3) (by norm_num) _)
  exact ⟨S, hS, hSle⟩

theorem twinYKind3_mid : TwinYKind3On TwinRowMid3 :=
  Q3TIV.twinYKind3_of_model fun t n _ hP => by
    rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact twinCentralizingNe3_odd le_rfl
    · exact twinCentralizingNe3_minus le_rfl

theorem twinYRank3_mid : TwinYRank3On TwinRowMid3 :=
  Q3TIV.twinYRank3_of_model
    (fun t n _ hP => by
      rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact twinRank3Model_odd le_rfl
      · exact twinRank3Model_minus le_rfl)
    (fun t n _ hP => by
      rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact twinCentralizingNe3_odd le_rfl
      · exact twinCentralizingNe3_minus le_rfl)
    smallNoThree3

theorem twinYType3On_mid_of_noCentral (h3 : OddThreeFreeInput)
    (hNC : TwinYNoCentral3On TwinRowMid3) : Q3TY.TwinYType3On TwinRowMid3 :=
  twinYType3On_of_inputs h3 hNC twinYKind3_mid twinYRank3_mid

end CFSG.ClassicalInvolution.Q3.Q3TIY
