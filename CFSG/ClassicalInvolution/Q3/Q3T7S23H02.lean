module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23H03
public import CFSG.ClassicalInvolution.Q3.Q3T7S23H04
public import CFSG.ClassicalInvolution.Asc77.AscT7L25
public import CFSG.ClassicalInvolution.Asc77.AscT7HC5
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Asc77

@[expose] def TwinCentralFact3 : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), StatedLieAdmissible t k 3 e →
    ((t = .PSL ∧ k = 4 ∧ 3 ^ e % 4 = 1) ∨ (t = .PSU ∧ k = 4 ∧ 3 ^ e % 4 = 3) ∨
      (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) →
    ∀ R ∈ ModelFund 3 t k e, ∀ R' ∈ ModelFund 3 t k e, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∀ x' ∈ R', x' * x' = 1 → x' ≠ 1 →
        x * x' ∈ Subgroup.center (modelUniv t k 3 e Fact.out).K →
        ∀ a ∈ R, a * a = x → ∀ b ∈ R', b * b = x' →
          ∃ R'' ∈ ModelFund 3 t k e, ∀ r ∈ R'', (a * b) * r = r * (a * b)

@[expose] def E4TwinGen3 : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), StatedLieAdmissible t k 3 e →
    ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4 ∧ 3 ^ e % 4 = 3) ∨
      (t = .PSU ∧ k = 4 ∧ 3 ^ e % 4 = 1)) →
    ∀ R ∈ ModelFund 3 t k e, ∀ R' ∈ ModelFund 3 t k e, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∀ x' ∈ R', x' * x' = 1 → x' ≠ 1 →
        x * x' ∈ Subgroup.center (modelUniv t k 3 e Fact.out).K →
        ∀ a ∈ R, a * a = x → ∀ b ∈ R', b * b = x' →
          (⊤ : Subgroup (modelUniv t k 3 e Fact.out).K) =
            Subgroup.center (modelUniv t k 3 e Fact.out).K ⊔
              (Subgroup.centralizer ({x} : Set (modelUniv t k 3 e Fact.out).K) ⊔
                Subgroup.centralizer ({a * b} : Set (modelUniv t k 3 e Fact.out).K) ⊔
                Subgroup.centralizer ({a⁻¹ * b} : Set (modelUniv t k 3 e Fact.out).K))


theorem five_le_three_pow {e : ℕ} (he : 2 ≤ e) : 5 ≤ 3 ^ e :=
  calc 5 ≤ 3 ^ 2 := by norm_num
    _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he

theorem twinCentralFact3_proved : TwinCentralFact3 := by
  intro t k e hadm htag
  have he1 : 1 ≤ e := hadm.2.1
  by_cases he : e = 1
  · subst he
    rcases htag with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd h (by norm_num)
    · exact Q3T7S23.twinCentralSU3 hadm
    · exact Q3T7S23.twinCentralSpin7_3
    · exact Q3T7S23.twinCentralD4P_3
    · exact Q3T7S23.twinCentralD4M_3 hadm
  · exact CFSG.ClassicalInvolution.Asc77.twinCentralFact_proved (p := 3) t k e hadm (by norm_num)
      (five_le_three_pow (by omega)) htag

theorem e4TwinGen3_proved : E4TwinGen3 := by
  intro t k e hadm htag
  have he1 : 1 ≤ e := hadm.2.1
  by_cases he : e = 1
  · subst he
    rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
    · exact Q3T7S23.e4GenSp_3 hadm
    · exact Q3T7S23.e4GenSL_3
    · exact absurd h (by norm_num)
  · exact CFSG.ClassicalInvolution.Asc77.e4TwinGen_proved (p := 3) t k e hadm (by norm_num)
      (five_le_three_pow (by omega)) htag

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
